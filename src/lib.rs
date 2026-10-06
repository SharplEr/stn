//! Parsing, semantic validation and bounded proof search for Semantic Types Notation.
//! See `doc.md` for the language and `README.md` for the search profiles.
mod model;
pub mod proof;
mod search;
pub mod syntax;

pub use model::{Type, TypeDisplay, TypeId, TypeStore};
pub use proof::{Cost, Proof, ProofId, ProofNode, ProofStore, Rule};
use std::{fmt, num::NonZeroUsize};

/// Selects the admitted intermediate types and bounds proof-search resources.
/// Explicitly declared shapes remain available regardless of the depth bound.
#[derive(Clone, Debug)]
pub struct ValidationOptions {
    /// Maximum nesting depth of synthesized anonymous collections and products.
    pub max_depth: usize,
    /// Positive maximum of distinct equal-minimum-cost proofs retained per pair.
    pub max_proofs: NonZeroUsize,
    /// Positive maximum of types admitted to the search universe.
    pub max_types: NonZeroUsize,
    /// Positive work budget shared by universe construction and proof search.
    pub max_steps: NonZeroUsize,
    /// Enumerate the complete constructor universe of doc.md §9.2. This can
    /// require exponentially many types even at depth zero (anonymous sums).
    pub exhaustive: bool,
}
impl Default for ValidationOptions {
    fn default() -> Self {
        Self {
            max_depth: 2,
            max_proofs: NonZeroUsize::new(5).unwrap(),
            max_types: NonZeroUsize::new(20_000).unwrap(),
            max_steps: NonZeroUsize::new(2_000_000).unwrap(),
            exhaustive: false,
        }
    }
}

/// A failure before feature search, or rejection of a supplied proof witness.
/// Resource exhaustion during search is recorded in the feature status instead.
#[derive(Debug)]
pub enum ValidationError {
    /// The document does not follow the concrete notation grammar.
    Parse(syntax::ParseError),
    /// Declarations or a supplied proof are invalid.
    Invalid(String),
    /// A finite parameter environment exceeds the elaboration safety limit.
    ExpansionLimit {
        /// One-based line of the declaration whose expansion exceeded the guard.
        line: usize,
        /// Maximum number of specializations allowed in one parameter environment.
        limit: usize,
    },
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

/// Outcome for one ground feature goal in the selected finite type universe.
/// An incomplete search does not establish that the goal is unresolvable.
#[derive(Clone, Debug)]
pub enum FeatureStatus {
    /// Minimum cost within the selected finite universe, independently checked.
    Proved {
        /// Retained distinct witnesses, all with the same minimum cost.
        proofs: Vec<ProofId>,
    },
    /// The selected universe was exhausted without a derivation of the goal.
    UnresolvableWithinUniverse {
        /// Explanation of the missing transformation or incompatible types.
        reason: String,
        /// A bounded sample of outputs reachable from the feature input.
        reachable: Vec<TypeId>,
    },
    /// A resource limit or failed witness check prevensourceted certification.
    SearchIncomplete {
        /// The condition that prevented the search from completing.
        reason: String,
    },
}
/// Signature, source location, and search outcome of one feature specialization.
/// Parameterized feature declarations produce a separate report for each choice.
#[derive(Clone, Debug)]
pub struct FeatureReport {
    /// Feature name, including concrete parameter substitutions when present.
    pub name: String,
    /// Logical input available to the proof search.
    pub input: TypeId,
    /// Exact semantic output required by the feature.
    pub output: TypeId,
    /// One-based line of the original feature declaration.
    pub line: usize,
    /// Checked witnesses or diagnostics for this ground goal.
    pub status: FeatureStatus,
}
/// Validation results and search bounds for an entire specification.
/// Its display representation is the text report written by the CLI.
#[derive(Clone, Debug)]
pub struct ValidationReport {
    /// Store owning every type identifier in the report and its proof DAGs.
    pub types: TypeStore,
    /// Store owning the proof identifiers reported for feature goals.
    pub proofs: ProofStore,
    /// Synthesized tuple-width bound inferred from declarations and trait lowering.
    pub max_tuple_arity: usize,
    /// Source label supplied at construction, normally the input path in the CLI.
    pub source_name: String,
    /// Universe profile and resource limits used for this validation run.
    pub options: ValidationOptions,
    /// Reports for all ground goals, in declaration and specialization order.
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
    /// Render goal signatures, certified proof costs, and profile-specific failure
    /// statuses using the report's owning stores to resolve all node identifiers.
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
                self.source_name,
                feature.line,
                feature.name,
                self.types.display(feature.input),
                self.types.display(feature.output)
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
                            self.proofs[*p].cost.functions,
                            self.proofs[*p].cost.rules,
                            self.proofs.expression(*p, &self.types)
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
                                .map(|t| self.types.display(*t).to_string())
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

/// Validate a UTF-8 specification and construct its report with the supplied
/// source label, used to identify the document in rendered diagnostics.
/// Parse and elaborate declarations before searching each ground feature goal.
/// Declaration failures return an error; proof-search exhaustion is represented
/// in feature statuses. The returned report owns both graphs needed by its IDs.
/// Consume the source `String` without copying its buffer. Lazy line preprocessing
/// borrows source slices and creates no copies of line substrings.
pub fn validate_source(
    source_name: impl Into<String>,
    source: String,
    options: &ValidationOptions,
) -> Result<ValidationReport, ValidationError> {
    syntax::SourceText::new(source)
        .parse()
        .map_err(ValidationError::from)
        .and_then(model::elaborate)
        .map(|specification| search::search(specification, options))
        .map(|result| result.into_report(source_name))
}
