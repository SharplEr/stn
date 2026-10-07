//! Incremental bounded proof search with independent minimum-cost certification.
mod bounds;
mod relation;
#[cfg(test)]
mod tests;
mod universe;

use crate::{
    FeatureReport, FeatureStatus, SearchUsage, Type, TypeId, TypeStore, ValidationOptions,
    ValidationReport,
    model::{Primitive, Specification},
    proof::ProofStore,
};
use indexmap::IndexSet;
use relation::ProofRelation;
use universe::IncrementalUniverse;

/// Exact endpoints in the owning type store; IDs stay stable as the domain grows.
type Pair = (TypeId, TypeId);

/// Work allowance shared by type generation, rule indexing, and agenda operations.
/// Exhaustion stops certification and yields an incomplete-search diagnostic.
struct Budget<'a> {
    /// Configured caps; depth and other search choices stay with the same options.
    options: &'a ValidationOptions,
    /// Counters owned by the result, surviving early returns and resource exhaustion.
    usage: &'a mut SearchUsage,
}
impl Budget<'_> {
    fn tick(&mut self) -> Result<(), String> {
        if self.usage.steps >= self.options.max_steps.get() {
            return Err("work limit reached; increase --max-steps".into());
        }
        self.usage.steps += 1;
        Ok(())
    }

    /// Record occupied type capacity while collecting explicit types in batches.
    /// An oversized batch fills the cap and stops construction; excess types are
    /// not admitted to a proof-search universe and do not count as budget usage.
    fn record_types(&mut self, count: usize) {
        self.usage.types = count.min(self.options.max_types.get());
    }

    /// Admit a new universe member without charging duplicates against the type cap.
    /// The bound applies to admitted search types, not every interned type node.
    fn insert_type(&mut self, known: &mut IndexSet<TypeId>, ty: TypeId) -> Result<bool, String> {
        if known.contains(&ty) {
            return Ok(false);
        }
        if known.len() >= self.options.max_types.get() {
            return Err(format!(
                "type limit ({}) reached; increase --max-types",
                self.options.max_types
            ));
        }
        known.insert(ty);
        self.record_types(known.len());
        Ok(true)
    }
}

/// Owner of the searched type graph, proof DAG, ground goals, and their outcomes.
/// Keeping these together preserves the stores required by every returned identifier.
pub(crate) struct SearchResult {
    /// Type nodes from elaboration and intermediate types interned during search.
    types: TypeStore,
    /// Checked witnesses retained for the feature outcomes.
    proofs: ProofStore,
    /// Ground feature signatures and substitutions, in specialization order.
    features: Vec<Primitive>,
    /// One outcome per ground feature, in the same order as `features`.
    statuses: Vec<FeatureStatus>,
    /// Synthesized tuple-width bound inferred from the consumed specification.
    tuple_arity: usize,
    /// Universe profile and resource limits used to obtain these outcomes.
    options: ValidationOptions,
    /// Accounted work and type capacity, retained even when a run is interrupted.
    usage: SearchUsage,
}

impl SearchResult {
    /// Retain reported witnesses and their premises, remapping every feature root
    /// to the compacted DAG. Interrupted searches retain no uncertified candidates.
    fn retain_feature_proofs(&mut self) -> Result<(), String> {
        let mut roots = self
            .statuses
            .iter()
            .filter_map(|status| match status {
                FeatureStatus::Proved { proofs } => Some(proofs.as_slice()),
                _ => None,
            })
            .flatten()
            .copied()
            .collect::<Vec<_>>();
        let mut budget = Budget {
            options: &self.options,
            usage: &mut self.usage,
        };
        self.proofs.retain_roots(&mut roots, || budget.tick())?;
        let mut roots = roots.into_iter();
        for status in &mut self.statuses {
            if let FeatureStatus::Proved { proofs } = status {
                for id in proofs {
                    *id = roots.next().expect("every reported root was retained");
                }
            }
        }
        Ok(())
    }

    /// Attach outcomes to ground goals and render their parameter substitutions.
    /// Transfer the owning graphs and search bounds into the report without cloning them.
    pub(crate) fn into_report(self, source_name: impl Into<String>) -> ValidationReport {
        let features = self
            .features
            .into_iter()
            .zip(self.statuses)
            .map(|(feature, status)| {
                let suffix = if feature.substitutions.is_empty() {
                    String::new()
                } else {
                    format!(
                        "<{}>",
                        feature
                            .substitutions
                            .iter()
                            .map(|(n, t)| format!("{n}={}", self.types.display(*t)))
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
        ValidationReport {
            types: self.types,
            proofs: self.proofs,
            max_tuple_arity: self.tuple_arity,
            source_name: source_name.into(),
            options: self.options,
            usage: self.usage,
            features,
        }
    }
}

/// Consume a checked specification and return one owner of its search results.
/// Any interrupted run makes all goals incomplete, so partial candidates cannot
/// be reported as certified minima. Compact successful roots and their premises
/// before returning, rewriting every reported identifier to the compacted store.
pub(crate) fn search(specification: Specification, options: ValidationOptions) -> SearchResult {
    let Specification {
        tuple_arity,
        mut types,
        primitives,
        features,
    } = specification;
    let mut proofs = ProofStore::default();
    let mut usage = SearchUsage::default();
    let statuses = run(
        &primitives,
        &features,
        &mut types,
        &mut proofs,
        &options,
        tuple_arity,
        &mut usage,
    )
    .unwrap_or_else(|reason| incomplete_statuses(features.len(), reason));
    let mut result = SearchResult {
        types,
        proofs,
        features,
        statuses,
        tuple_arity,
        options,
        usage,
    };
    if let Err(reason) = result.retain_feature_proofs() {
        result.statuses = incomplete_statuses(result.features.len(), reason);
        result.proofs = ProofStore::default();
    }
    result
}

/// Convert an interrupted run into uncertified outcomes for every requested goal.
fn incomplete_statuses(count: usize, reason: String) -> Vec<FeatureStatus> {
    vec![FeatureStatus::SearchIncomplete { reason }; count]
}

/// Owning search session over a growing domain. Lower bounds refer to the complete
/// planned domain; the relation contains only currently generated and activated endpoints.
struct SearchState<'a> {
    universe: IncrementalUniverse,
    relation: ProofRelation<'a>,
    goals: Vec<Pair>,
    bounds: std::collections::HashMap<Pair, crate::proof::Cost>,
    early_ceiling: crate::proof::Cost,
}

impl<'a> SearchState<'a> {
    /// Prepare the explicit domain and safe goal bounds, then seed its rule relationships.
    fn new(
        primitives: &[Primitive],
        features: &[Primitive],
        types: &'a mut TypeStore,
        proofs: &'a mut ProofStore,
        tuple_arity: usize,
        mut budget: Budget<'a>,
    ) -> Result<Self, String> {
        let universe =
            IncrementalUniverse::new(primitives, features, types, tuple_arity, &mut budget)?;
        let goals = features
            .iter()
            .map(|p| (p.input, p.output))
            .collect::<Vec<_>>();
        let bounds =
            bounds::lower_bounds(&goals, &universe.members, primitives, types, &mut budget)?;
        let early_ceiling = bounds.values().copied().max().expect("at least one goal");
        let mut relation = ProofRelation::new(types, proofs, budget);
        relation.activate(&universe.members.iter().copied().collect::<Vec<_>>())?;
        relation.seed_primitives(primitives)?;
        Ok(Self {
            universe,
            relation,
            goals,
            bounds,
            early_ceiling,
        })
    }

    /// Alternate bounded proof and generation batches. Before domain completion, defer
    /// proof work too expensive to reach any lower bound; newly enabled cheaper routes
    /// can then arrive before expensive witnesses spread through the relation.
    fn solve(&mut self) -> Result<(), String> {
        while !self.is_finished() {
            self.propagate_batch()?;
            if !self.is_finished() && !self.universe.is_complete() {
                let additions = self
                    .universe
                    .advance(self.relation.types, &mut self.relation.budget)?;
                self.relation.activate(&additions)?;
            }
        }
        Ok(())
    }

    /// Process only pending proofs useful in the current phase, without starving generation.
    fn propagate_batch(&mut self) -> Result<(), String> {
        for _ in 0..64 {
            if self.is_finished()
                || (!self.universe.is_complete()
                    && !self.relation.can_attain_bound(self.early_ceiling))
                || !self.relation.propagate()?
            {
                break;
            }
        }
        Ok(())
    }

    /// A lower-bound match can finish before generation. Otherwise require complete
    /// generation and activation, then saturation through every goal's best-known cost.
    fn is_finished(&self) -> bool {
        self.relation.meets_bounds(&self.bounds)
            || (self.universe.is_complete() && self.relation.is_saturated_for(&self.goals))
    }
}

/// Search all goals in one shared session and independently check its final witnesses.
/// Limits propagate to the owning result, which makes every goal incomplete.
fn run(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    proofs: &mut ProofStore,
    options: &ValidationOptions,
    tuple_arity: usize,
    usage: &mut SearchUsage,
) -> Result<Vec<FeatureStatus>, String> {
    if features.is_empty() {
        return Ok(Vec::new());
    }
    let budget = Budget { options, usage };
    let mut state = SearchState::new(primitives, features, types, proofs, tuple_arity, budget)?;
    state.solve()?;
    state.relation.check_features(primitives, features)
}

/// Explain common missing steps using the bounded sample of reachable outputs:
/// nominal construction, scalar error handling, or flat-product construction.
/// This diagnostic supplements the exhausted relation; it is not a separate
/// derivability test and cannot establish failure outside the selected universe.
fn failure_reason(target: TypeId, reachable: &[TypeId], types: &TypeStore) -> String {
    let target_text = types.display(target);
    if matches!(types[target], Type::Named(..))
        && reachable.iter().any(|t| *t == types.shape(target))
    {
        return format!(
            "the structural shape of {target_text} is reachable, but no nominal constructor is available; declare a morphism returning {target_text}"
        );
    }
    if reachable
        .iter()
        .any(|t| matches!(&types[*t], Type::Sum(v) if v.contains(&target)))
    {
        return format!(
            "a sum containing {target_text} is reachable; unhandled alternatives cannot be discarded from a scalar result"
        );
    }
    if matches!(&types[target], Type::Product(v) if v.len() > 2) {
        return "no path produces the required flat product; fanout creates binary products and does not flatten tuples".into();
    }
    "no derivation reaches the exact output type in the selected universe; declare a missing transformation or name an intermediate type".into()
}
