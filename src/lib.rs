//! Parsing, semantic validation and bounded proof search for Semantic Types Notation.
//! See `doc.md` for the language and `README.md` for the search profiles.
mod model;
pub mod proof;
mod search;
pub mod syntax;

pub use model::Type;
pub use proof::{Cost, Proof, ProofNode, Rule};
use std::{fmt, sync::Arc};

#[derive(Clone, Debug)]
pub struct ValidationOptions {
    pub max_depth: usize,
    pub max_proofs: usize,
    pub max_types: usize,
    pub max_steps: usize,
    /// Enumerate the complete constructor universe of doc.md §9.2. This can
    /// require exponentially many types even at depth zero (anonymous sums).
    pub exhaustive: bool,
}
impl Default for ValidationOptions {
    fn default() -> Self {
        Self {
            max_depth: 2,
            max_proofs: 5,
            max_types: 20_000,
            max_steps: 2_000_000,
            exhaustive: false,
        }
    }
}

#[derive(Debug)]
pub enum ValidationError {
    Parse(syntax::ParseError),
    Invalid(String),
    ExpansionLimit { line: usize, limit: usize },
}
impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Parse(error) => write!(f, "PARSE_ERROR {error}"),
            Self::Invalid(message) => write!(f, "INVALID_SPECIFICATION {message}"),
            Self::ExpansionLimit { line, limit } => write!(
                f,
                "EXPANSION_LIMIT line {line}: more than {limit} specializations in one declaration"
            ),
        }
    }
}
impl std::error::Error for ValidationError {}
impl From<syntax::ParseError> for ValidationError {
    fn from(error: syntax::ParseError) -> Self {
        Self::Parse(error)
    }
}

#[derive(Clone, Debug)]
pub enum FeatureStatus {
    /// Minimum cost within the selected finite universe, independently checked.
    Proved {
        proofs: Vec<Arc<Proof>>,
    },
    UnresolvableWithinUniverse {
        reason: String,
        reachable: Vec<Type>,
    },
    SearchIncomplete {
        reason: String,
    },
}
#[derive(Clone, Debug)]
pub struct FeatureReport {
    pub name: String,
    pub input: Type,
    pub output: Type,
    pub line: usize,
    pub status: FeatureStatus,
}
#[derive(Clone, Debug)]
pub struct ValidationReport {
    pub max_tuple_arity: usize,
    pub source_name: String,
    pub options: ValidationOptions,
    pub features: Vec<FeatureReport>,
}
impl ValidationReport {
    pub fn has_unresolved_features(&self) -> bool {
        self.features
            .iter()
            .any(|f| !matches!(f.status, FeatureStatus::Proved { .. }))
    }
    pub fn has_incomplete_search(&self) -> bool {
        self.features
            .iter()
            .any(|f| matches!(f.status, FeatureStatus::SearchIncomplete { .. }))
    }
}
impl fmt::Display for ValidationReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Semantic Types Notation: {}", self.source_name)?;
        writeln!(
            f,
            "universe={}, max-depth={}, max-tuple-arity={}, max-proofs={}, max-types={}, max-steps={}",
            if self.options.exhaustive {
                "exhaustive"
            } else {
                "relevant"
            },
            self.options.max_depth,
            self.max_tuple_arity,
            self.options.max_proofs,
            self.options.max_types,
            self.options.max_steps
        )?;
        if !self.options.exhaustive {
            writeln!(
                f,
                "Costs and failures refer to the relevant universe; the complete depth-bounded universe was not enumerated."
            )?;
        }
        for feature in &self.features {
            writeln!(
                f,
                "\n{}:{}: {}: {} -> {}",
                self.source_name, feature.line, feature.name, feature.input, feature.output
            )?;
            match &feature.status {
                FeatureStatus::Proved { proofs } => {
                    writeln!(
                        f,
                        "  PROVED ({} minimum-cost witness(es) in the selected universe)",
                        proofs.len()
                    )?;
                    for p in proofs {
                        writeln!(
                            f,
                            "  [{}, {}] {}",
                            p.cost.functions,
                            p.cost.rules,
                            p.expression()
                        )?;
                    }
                }
                FeatureStatus::UnresolvableWithinUniverse { reason, reachable } => {
                    writeln!(
                        f,
                        "  {}: {reason}",
                        if self.options.exhaustive {
                            "UNRESOLVABLE_WITHIN_BOUNDS"
                        } else {
                            "UNRESOLVABLE_IN_RELEVANT_UNIVERSE"
                        }
                    )?;
                    if !reachable.is_empty() {
                        writeln!(
                            f,
                            "  reachable (up to 16): {}",
                            reachable
                                .iter()
                                .map(ToString::to_string)
                                .collect::<Vec<_>>()
                                .join("; ")
                        )?;
                    }
                    if !self.options.exhaustive {
                        writeln!(
                            f,
                            "  Try --exhaustive to check the complete universe, or declare an intermediate type."
                        )?;
                    }
                }
                FeatureStatus::SearchIncomplete { reason } => {
                    writeln!(f, "  SEARCH_INCOMPLETE: {reason}")?
                }
            }
        }
        Ok(())
    }
}

pub fn validate_source(
    source: &str,
    options: &ValidationOptions,
) -> Result<ValidationReport, ValidationError> {
    if options.max_proofs == 0 || options.max_types == 0 || options.max_steps == 0 {
        return Err(ValidationError::Invalid(
            "max_proofs, max_types and max_steps must be positive".into(),
        ));
    }
    let document = syntax::parse(source)?;
    let model::Specification {
        tuple_arity,
        types,
        primitives,
        features,
    } = model::elaborate(&document)?;
    let statuses = search::search(&primitives, &features, &types, options, tuple_arity);
    let reports = features
        .into_iter()
        .zip(statuses)
        .map(|(feature, status)| {
            let suffix = if feature.substitutions.is_empty() {
                String::new()
            } else {
                format!(
                    "<{}>",
                    feature
                        .substitutions
                        .iter()
                        .map(|(n, t)| format!("{n}={t}"))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            FeatureReport {
                name: format!("{}{suffix}", feature.name),
                input: feature.input,
                output: feature.output,
                line: feature.line,
                status,
            }
        })
        .collect();
    Ok(ValidationReport {
        max_tuple_arity: tuple_arity,
        source_name: "input".into(),
        options: options.clone(),
        features: reports,
    })
}

/// Verify an externally stored or modified witness against a specification.
/// This checks semantic rule instances and costs, independently of search
/// limits. It does not assert that the proof has minimum cost.
pub fn check_proof(source: &str, proof: &Arc<Proof>) -> Result<(), ValidationError> {
    let document = syntax::parse(source)?;
    let specification = model::elaborate(&document)?;
    proof::check(proof, &specification.primitives, &specification.types)
        .map_err(ValidationError::Invalid)
}
