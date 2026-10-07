//! A finite type universe and a shortest-path agenda over inference hyperedges.
use crate::{
    FeatureReport, FeatureStatus, Type, TypeId, TypeStore, ValidationOptions, ValidationReport,
    model::{Primitive, Specification},
    proof::{self, Cost, NormalForms, NormalId, Proof, ProofId, ProofStore, Rule},
};
use indexmap::IndexSet;
use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, HashSet},
};

/// Input/output pair of type identifiers interned in the search universe.
type Pair = (usize, usize);
/// Unary rule instances indexed by their required child morphism's type pair.
/// Each entry lists the resulting pair and the rule that produces it.
/// Only key lookup is used; premise order comes from the search agenda.
type LiftIndex = HashMap<Pair, Vec<(Pair, Rule)>>;

/// Work allowance shared by type generation, rule indexing, and agenda operations.
/// Exhaustion stops certification and yields an incomplete-search diagnostic.
struct Budget {
    /// Number of accounted work units that can still be consumed.
    remaining: usize,
}
impl Budget {
    fn tick(&mut self) -> Result<(), String> {
        self.remaining = self
            .remaining
            .checked_sub(1)
            .ok_or("work limit reached; increase --max-steps")?;
        Ok(())
    }
}

/// Admit a new universe member without charging duplicates against the type cap.
/// The bound applies to admitted search types, not every node interned in the store.
fn insert_type(
    known: &mut IndexSet<TypeId>,
    ty: TypeId,
    options: &ValidationOptions,
) -> Result<bool, String> {
    if known.contains(&ty) {
        return Ok(false);
    }
    if known.len() >= options.max_types.get() {
        return Err(format!(
            "type limit ({}) reached; increase --max-types",
            options.max_types
        ));
    }
    known.insert(ty);
    Ok(true)
}

/// Collect all ground declarations, callable endpoints, feature goals, and their
/// subexpressions, repeatedly exposing newly discovered direct nominal bodies.
/// Explicit shapes bypass the synthesized-depth bound but still obey the type cap.
/// Preserve discovery order so universe construction stays deterministic.
fn explicit_types(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    options: &ValidationOptions,
) -> Result<IndexSet<TypeId>, String> {
    let mut out = IndexSet::new();
    for p in primitives.iter().chain(features) {
        types.collect(p.input, &mut out);
        types.collect(p.output, &mut out);
    }
    types.collect_declarations(&mut out, options.max_types.get())?;
    // Include direct nominal bodies recursively, including predefined Bytes.
    loop {
        let before = out.len();
        for t in out.clone() {
            types.collect(types.shape(t), &mut out);
        }
        if out.len() > options.max_types.get() {
            return Err("explicit types exceed --max-types".into());
        }
        if before == out.len() {
            break;
        }
    }
    Ok(out)
}

/// Seed elementary universe transformations from directed nominal views and product
/// projections. These pairs guide type generation; they are not proof witnesses.
fn structural_steps(known: &IndexSet<TypeId>, types: &TypeStore) -> IndexSet<(TypeId, TypeId)> {
    let mut steps = IndexSet::new();
    for &t in known {
        let shape = types.shape(t);
        if shape != t {
            steps.insert((t, shape));
        }
        if let Type::Product(items) = &types[shape] {
            for &item in items {
                steps.insert((t, item));
            }
        }
    }
    steps
}

/// Admit explicit products and close existing collections and sums under
/// elementary transformations, rather than enumerating the full depth grammar.
/// Iterate to a fixed point using user signatures, views, projections, collection
/// lifts, flattening, narrowing, and carried sum alternatives. Newly synthesized
/// shapes obey the depth bound; resource exhaustion prevents certification.
fn relevant_universe(
    explicit: &IndexSet<TypeId>,
    primitives: &[Primitive],
    types: &mut TypeStore,
    options: &ValidationOptions,
    budget: &mut Budget,
) -> Result<IndexSet<TypeId>, String> {
    let mut known = explicit.clone();
    let mut steps = structural_steps(explicit, types);
    steps.extend(primitives.iter().map(|p| (p.input, p.output)));
    for primitive in primitives {
        for &source in explicit {
            if types.accepts(primitive.input, source) {
                steps.insert((source, primitive.output));
            }
        }
    }
    loop {
        let mut additions = IndexSet::new();
        let mut new_steps = IndexSet::new();
        // Collection rules share depth admission and directed nominal targets.
        // Pass the pending sets explicitly so sum extension can update them too.
        let add_collection_step =
            |source,
             node,
             types: &mut TypeStore,
             additions: &mut IndexSet<TypeId>,
             new_steps: &mut IndexSet<(TypeId, TypeId)>| {
                let target = types.intern(node);
                if explicit.contains(&target) || types.depth(target) <= options.max_depth {
                    additions.insert(target);
                    nominal_steps(source, target, &known, types, new_steps);
                    new_steps.insert((source, target));
                }
            };
        for &(a, b) in &steps {
            let handled = types.handled_variants(a);
            for &source in &known {
                budget.tick()?;
                let variants = types.source_variants(source);
                if source != a && handled.is_subset(&variants) {
                    let target = types.union(
                        std::iter::once(b)
                            .chain(variants.difference(&handled).copied())
                            .collect(),
                    );
                    if explicit.contains(&target) || types.depth(target) <= options.max_depth {
                        additions.insert(target);
                        new_steps.insert((source, target));
                    }
                }
                let shape = types.shape(source);
                let mapped = match types[shape] {
                    Type::List(t) if t == a => Some(Type::List(b)),
                    Type::Set(t) if t == a => Some(Type::Set(b)),
                    Type::Map(k, t) if t == a => Some(Type::Map(k, b)),
                    _ => None,
                };
                let flattened = match (&types[shape], &types[b]) {
                    (Type::List(t), Type::List(result)) if *t == a => Some(Type::List(*result)),
                    _ => None,
                };
                for node in [mapped, flattened].into_iter().flatten() {
                    add_collection_step(source, node, types, &mut additions, &mut new_steps);
                }
            }
        }
        // Narrow only towards explicitly available element alternatives.
        for &source in &known {
            let shape = types.shape(source);
            for &target in &known {
                budget.tick()?;
                let candidate = match types[shape] {
                    Type::List(item) | Type::Set(item)
                        if types
                            .source_variants(target)
                            .is_subset(&types.source_variants(item)) =>
                    {
                        Some(if matches!(types[shape], Type::List(_)) {
                            Type::List(target)
                        } else {
                            Type::Set(target)
                        })
                    }
                    Type::Map(key, value)
                        if types
                            .source_variants(target)
                            .is_subset(&types.source_variants(key)) =>
                    {
                        Some(Type::Map(target, value))
                    }
                    _ => None,
                };
                if let Some(node) = candidate {
                    add_collection_step(source, node, types, &mut additions, &mut new_steps);
                }
            }
        }
        let old_steps = steps.len();
        steps.extend(new_steps);
        let mut changed = false;
        for t in additions {
            changed |= insert_type(&mut known, t, options)?;
        }
        if !changed && old_steps == steps.len() {
            return Ok(known);
        }
    }
}

/// Add declared nominal targets matching a changed collection result shape.
/// Only nominal sources can use this route, and preserving a shape cannot grant
/// a different nominal identity. This mirrors the proof checker's lift guard.
fn nominal_steps(
    source: TypeId,
    result_shape: TypeId,
    known: &IndexSet<TypeId>,
    types: &TypeStore,
    steps: &mut IndexSet<(TypeId, TypeId)>,
) {
    if matches!(types[source], Type::Named(..)) && types.shape(source) != result_shape {
        for &target in known {
            if matches!(types[target], Type::Named(..)) && types.shape(target) == result_shape {
                steps.insert((source, target));
            }
        }
    }
}

/// Enumerate every nonempty subset of the candidate alternatives as a normalized
/// union. Incremental subset construction avoids fixed-width bit-mask limits;
/// the work and type caps stop its potentially exponential growth explicitly.
fn add_sums(
    known: &mut IndexSet<TypeId>,
    candidates: &[TypeId],
    types: &mut TypeStore,
    options: &ValidationOptions,
    budget: &mut Budget,
) -> Result<(), String> {
    // Incremental powerset generation has no word-size-dependent bit masks.
    let mut sums = IndexSet::<TypeId>::new();
    for &atom in candidates {
        let mut next = vec![atom];
        for &sum in &sums {
            budget.tick()?;
            next.push(types.union(vec![sum, atom]));
        }
        for sum in next {
            insert_type(known, sum, options)?;
            sums.insert(sum);
        }
    }
    Ok(())
}

/// Enumerate the complete constructor universe within the depth and tuple-width
/// bounds, retaining explicit shapes even when they exceed the synthesis depth.
/// Start with atoms and their sums, then add collections, ordered products, and
/// their sums at each depth. Resource caps can interrupt this exhaustive profile.
fn exhaustive_universe(
    explicit: &IndexSet<TypeId>,
    types: &mut TypeStore,
    options: &ValidationOptions,
    budget: &mut Budget,
    arity: usize,
) -> Result<IndexSet<TypeId>, String> {
    let mut known = explicit.clone();
    insert_type(&mut known, types.intern(Type::Unit), options)?;
    let atoms = known
        .iter()
        .copied()
        .filter(|t| matches!(types[*t], Type::Named(..) | Type::Exists(..) | Type::Unit))
        .collect::<Vec<_>>();
    add_sums(&mut known, &atoms, types, options, budget)?;
    for depth in 1..=options.max_depth {
        let inner = known
            .iter()
            .copied()
            .filter(|t| types.depth(*t) < depth)
            .collect::<Vec<_>>();
        for &a in &inner {
            budget.tick()?;
            insert_type(&mut known, types.intern(Type::List(a)), options)?;
            insert_type(&mut known, types.intern(Type::Set(a)), options)?;
            for &b in &inner {
                budget.tick()?;
                insert_type(&mut known, types.intern(Type::Map(a, b)), options)?;
            }
        }
        let mut tuples = vec![Vec::new()];
        for width in 1..=arity {
            let mut next = Vec::new();
            for prefix in tuples {
                for &t in &inner {
                    budget.tick()?;
                    let mut tuple = prefix.clone();
                    tuple.push(t);
                    if width >= 2 {
                        insert_type(
                            &mut known,
                            types.intern(Type::Product(tuple.clone())),
                            options,
                        )?;
                    }
                    next.push(tuple);
                }
            }
            tuples = next;
        }
        let nonsums = known
            .iter()
            .copied()
            .filter(|t| !matches!(types[*t], Type::Sum(_)) && types.depth(*t) <= depth)
            .collect::<Vec<_>>();
        add_sums(&mut known, &nonsums, types, options, budget)?;
    }
    Ok(known)
}

/// Pending proof identifiers for generalized Dijkstra search over type pairs.
/// Interned identifiers break equal-cost ties in deterministic insertion order.
/// Offered costs are tentative until a candidate settles.
struct Agenda<'a> {
    /// Fixed type universe used to translate indexed pairs into proof endpoints.
    universe: &'a SearchUniverse,
    /// Shared storage for pending and settled proof records.
    proofs: &'a mut ProofStore,
    /// Work allowance remaining after universe construction.
    budget: Budget,
    /// Maximum normalized alternatives offered at the best cost for each pair.
    limit: usize,
    /// Minimum-cost queue; proof records live exclusively in the proof store.
    heap: BinaryHeap<Reverse<(Cost, ProofId)>>,
    /// Lowest candidate cost offered so far for each input/output type pair.
    best_offered: HashMap<Pair, Cost>,
    /// Normalized compositions offered at each pair's best cost.
    seen: HashMap<Pair, HashSet<NormalId>>,
    /// Typed equivalence keys, shared by accepted premises and new candidates.
    normal_forms: NormalForms,
}
impl<'a> Agenda<'a> {
    fn new(
        universe: &'a SearchUniverse,
        proofs: &'a mut ProofStore,
        budget: Budget,
        limit: usize,
    ) -> Self {
        Self {
            universe,
            proofs,
            budget,
            limit,
            heap: BinaryHeap::new(),
            best_offered: HashMap::new(),
            seen: HashMap::new(),
            normal_forms: NormalForms::default(),
        }
    }
    /// Offer a candidate at its pair's best known cost, resetting alternatives
    /// when a cheaper cost arrives. Equivalent compositions share one alternative
    /// before the limit is applied. Reject worse, duplicate, or excess candidates
    /// before inserting records; settlement later establishes minimum costs.
    fn offer(&mut self, pair: Pair, candidate: Proof, types: &TypeStore) -> Result<(), String> {
        self.budget.tick()?;
        if self
            .best_offered
            .get(&pair)
            .is_some_and(|best| *best < candidate.cost)
        {
            return Ok(());
        }
        if self
            .best_offered
            .get(&pair)
            .is_none_or(|best| *best > candidate.cost)
        {
            self.best_offered.insert(pair, candidate.cost);
            self.seen.remove(&pair);
        }
        let alternatives = self.seen.entry(pair).or_default();
        if alternatives.len() >= self.limit {
            return Ok(());
        }
        let normal = self.normal_forms.candidate(&candidate, types);
        if !alternatives.insert(normal) {
            return Ok(());
        }
        let cost = candidate.cost;
        let id = self.proofs.insert(candidate);
        self.normal_forms.remember(id, normal);
        self.heap.push(Reverse((cost, id)));
        Ok(())
    }

    /// Construct an inference using indexed endpoints and offer it at its computed cost.
    fn infer(
        &mut self,
        pair: Pair,
        rule: Rule,
        children: Vec<ProofId>,
        types: &TypeStore,
    ) -> Result<(), String> {
        let candidate = self.proofs.inference(
            self.universe.members[pair.0],
            self.universe.members[pair.1],
            rule,
            children,
        );
        self.offer(pair, candidate, types)
    }

    fn pop(&mut self) -> Option<ProofId> {
        let Reverse((_, id)) = self.heap.pop()?;
        Some(id)
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
}

impl SearchResult {
    /// Retain reported witnesses and their premises, remapping every feature root
    /// to the compacted DAG. Interrupted searches retain no uncertified candidates.
    fn retain_feature_proofs(&mut self) {
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
        self.proofs.retain_roots(&mut roots);
        let mut roots = roots.into_iter();
        for status in &mut self.statuses {
            if let FeatureStatus::Proved { proofs } = status {
                for id in proofs {
                    *id = roots.next().expect("every reported root was retained");
                }
            }
        }
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
    let statuses = run(
        &primitives,
        &features,
        &mut types,
        &mut proofs,
        &options,
        tuple_arity,
    )
    .unwrap_or_else(|reason| incomplete_statuses(features.len(), reason));
    let mut result = SearchResult {
        types,
        proofs,
        features,
        statuses,
        tuple_arity,
        options,
    };
    result.retain_feature_proofs();
    result
}

/// Convert an interrupted run into uncertified outcomes for every requested goal.
fn incomplete_statuses(count: usize, reason: String) -> Vec<FeatureStatus> {
    vec![FeatureStatus::SearchIncomplete { reason }; count]
}

/// Finite search universe with deterministic ordering and dense local indices.
/// The type store may intern more nodes, but only these members can be proof endpoints.
struct SearchUniverse {
    /// Admitted types sorted by semantic structure, independent of allocation order.
    /// The set provides both indexed access and reverse lookup by type identifier.
    members: IndexSet<TypeId>,
    /// Direct structural view of each member, cached for rule preparation.
    shapes: Vec<TypeId>,
}

impl SearchUniverse {
    /// Generate the selected bounded universe, then assign stable indices for rule lookup.
    fn build(
        primitives: &[Primitive],
        features: &[Primitive],
        types: &mut TypeStore,
        options: &ValidationOptions,
        tuple_arity: usize,
        budget: &mut Budget,
    ) -> Result<Self, String> {
        let explicit = explicit_types(primitives, features, types, options)?;
        let mut members = if options.exhaustive {
            exhaustive_universe(&explicit, types, options, budget, tuple_arity)?
        } else {
            relevant_universe(&explicit, primitives, types, options, budget)?
        };
        members.sort_unstable_by(|a, b| types.compare(*a, *b));
        let shapes = members.iter().map(|t| types.shape(*t)).collect();
        Ok(Self { members, shapes })
    }

    /// Find the local index of a type required to belong to this universe.
    fn index_of(&self, ty: TypeId) -> usize {
        self.members
            .get_index_of(&ty)
            .expect("type belongs to the search universe")
    }

    /// Translate endpoints known to belong to this universe into a search key.
    fn pair(&self, input: TypeId, output: TypeId) -> Pair {
        (self.index_of(input), self.index_of(output))
    }
}

/// Prepared inference relationships that remain fixed throughout proof search.
/// Indices select applicable rules without rescanning the entire type universe.
struct RuleIndex {
    /// Collection lifts keyed by the element-level morphism they require.
    lifts: LiftIndex,
    /// Narrower inputs accepted by a morphism with the indexed input type.
    restrictions: Vec<Vec<usize>>,
    /// Sum inputs containing all alternatives handled by the indexed input type.
    sums: Vec<Vec<usize>>,
    /// Admitted anonymous binary products keyed by their ordered component indices.
    fanouts: HashMap<Pair, usize>,
}

impl RuleIndex {
    fn new(type_count: usize) -> Self {
        Self {
            lifts: LiftIndex::new(),
            restrictions: vec![Vec::new(); type_count],
            sums: vec![Vec::new(); type_count],
            fanouts: HashMap::new(),
        }
    }

    /// Register only anonymous binary products as results constructible by fanout.
    fn index_product(&mut self, index: usize, universe: &SearchUniverse, types: &TypeStore) {
        if let Type::Product(items) = &types[universe.members[index]] {
            if let [left, right] = items.as_slice() {
                self.fanouts.insert(universe.pair(*left, *right), index);
            }
        }
    }

    /// Index input adaptation and collection lifting for one ordered pair of types.
    /// Nominal collection targets must obey the directed construction rules.
    fn index_pair(&mut self, pair: Pair, universe: &SearchUniverse, types: &TypeStore) {
        let (i, j) = pair;
        let (a, b) = (universe.members[i], universe.members[j]);
        if a != b && types.accepts(a, b) {
            self.restrictions[i].push(j);
        }
        if a != b
            && types
                .handled_variants(a)
                .is_subset(&types.source_variants(b))
        {
            self.sums[i].push(j);
        }
        let (source_shape, target_shape) = (universe.shapes[i], universe.shapes[j]);
        if !proof::collection_target_allowed(a, b, source_shape, target_shape, types) {
            return;
        }
        let premise = match (&types[source_shape], &types[target_shape]) {
            (Type::List(s), Type::List(t)) => Some((s, t, Rule::MapList)),
            (Type::Set(s), Type::Set(t)) => Some((s, t, Rule::MapSet)),
            (Type::Map(k, s), Type::Map(l, t)) if k == l => Some((s, t, Rule::MapValues)),
            _ => None,
        };
        if let Some((s, t, rule)) = premise {
            if let (Some(l), Some(r)) = (
                universe.members.get_index_of(s),
                universe.members.get_index_of(t),
            ) {
                self.lifts.entry((l, r)).or_default().push((pair, rule));
            }
        }
        if let (Type::List(s), Type::List(_)) = (&types[source_shape], &types[target_shape]) {
            if let (Some(l), Some(r)) = (
                universe.members.get_index_of(s),
                universe.members.get_index_of(&target_shape),
            ) {
                self.lifts
                    .entry((l, r))
                    .or_default()
                    .push((pair, Rule::FlatMap));
            }
        }
    }
}

/// One search over a fixed universe: pending candidates, settled witnesses, and rule indices.
/// The owning stores are borrowed for the run; proofs refer to shared nodes by identifier.
struct ProofSearch<'a> {
    /// Admitted endpoints and their dense local indices.
    universe: &'a SearchUniverse,
    /// Shared type graph, also used to normalize results of sum extension.
    types: &'a mut TypeStore,
    /// Candidate queue, proof storage, alternative limit, and remaining work budget.
    agenda: Agenda<'a>,
    /// Structural relationships prepared before processing the queue.
    rules: RuleIndex,
    /// Accepted minimum-cost witnesses for each derivable type pair.
    settled: HashMap<Pair, Vec<ProofId>>,
    /// Settled output indices for each input, in discovery order.
    outgoing: Vec<IndexSet<usize>>,
    /// Settled input indices for each output, in discovery order.
    incoming: Vec<IndexSet<usize>>,
}

impl<'a> ProofSearch<'a> {
    fn new(
        universe: &'a SearchUniverse,
        types: &'a mut TypeStore,
        proofs: &'a mut ProofStore,
        budget: Budget,
        max_proofs: usize,
    ) -> Self {
        let type_count = universe.members.len();
        Self {
            universe,
            types,
            agenda: Agenda::new(universe, proofs, budget, max_proofs),
            rules: RuleIndex::new(type_count),
            settled: HashMap::new(),
            outgoing: vec![IndexSet::new(); type_count],
            incoming: vec![IndexSet::new(); type_count],
        }
    }

    /// Prepare rule lookups and seed proofs in deterministic type and declaration order.
    /// Budget charges and candidate insertion order also determine bounded-run outcomes.
    fn prepare(&mut self, primitives: &[Primitive]) -> Result<(), String> {
        for source in 0..self.universe.members.len() {
            self.seed_structural(source)?;
            self.rules.index_product(source, self.universe, self.types);
            for target in 0..self.universe.members.len() {
                self.agenda.budget.tick()?;
                self.rules
                    .index_pair((source, target), self.universe, self.types);
                self.seed_narrowing((source, target))?;
            }
        }
        for (id, primitive) in primitives.iter().enumerate() {
            let pair = self.universe.pair(primitive.input, primitive.output);
            self.agenda
                .offer(pair, Proof::primitive(id, primitive), self.types)?;
        }
        Ok(())
    }

    /// Seed identity, the direct nominal view, and all available product projections.
    fn seed_structural(&mut self, source: usize) -> Result<(), String> {
        self.agenda
            .infer((source, source), Rule::Identity, vec![], self.types)?;
        let shape = self.universe.shapes[source];
        if shape != self.universe.members[source] {
            if let Some(target) = self.universe.members.get_index_of(&shape) {
                self.agenda
                    .infer((source, target), Rule::View, vec![], self.types)?;
            }
        }
        if let Type::Product(items) = &self.types[shape] {
            for (component, item) in items.iter().enumerate() {
                let target = self.universe.index_of(*item);
                self.agenda.infer(
                    (source, target),
                    Rule::Project(component),
                    vec![],
                    self.types,
                )?;
            }
        }
        Ok(())
    }

    /// Seed the collection-narrowing rules whose endpoint contracts hold for this pair.
    fn seed_narrowing(&mut self, pair: Pair) -> Result<(), String> {
        if pair.0 == pair.1 {
            return Ok(());
        }
        let (input, output) = (self.universe.members[pair.0], self.universe.members[pair.1]);
        for rule in [Rule::NarrowList, Rule::NarrowSet, Rule::NarrowKeys] {
            if proof::seed_valid(rule, input, output, self.types) {
                self.agenda.infer(pair, rule, vec![], self.types)?;
            }
        }
        Ok(())
    }

    /// Settle candidates by increasing cost and derive their immediate consequences.
    /// Stop after all goal minima and their retained equal-cost alternatives are settled.
    fn solve(&mut self, features: &[Primitive]) -> Result<(), String> {
        let goals = features
            .iter()
            .map(|feature| self.universe.pair(feature.input, feature.output))
            .collect::<Vec<_>>();
        while let Some(proof) = self.agenda.pop() {
            let candidate = &self.agenda.proofs[proof];
            let pair = self.universe.pair(candidate.input, candidate.output);
            let cost = candidate.cost;
            self.agenda.budget.tick()?;
            if self.goals_finished(&goals, cost) {
                break;
            }
            if self.settle(pair, proof) {
                self.derive(pair, proof)?;
            }
        }
        Ok(())
    }

    /// A more expensive candidate cannot improve completed goals: every inference
    /// costs strictly more than each premise. Equal-cost candidates are still processed.
    fn goals_finished(&self, goals: &[Pair], next_cost: Cost) -> bool {
        if !goals.iter().all(|goal| self.settled.contains_key(goal)) {
            return false;
        }
        goals
            .iter()
            .map(|goal| self.agenda.proofs[self.settled[goal][0]].cost)
            .max()
            .is_some_and(|last_goal| next_cost > last_goal)
    }

    /// Accept a minimum-cost alternative and update both composition lookup directions.
    /// More expensive or excess alternatives remain unused in the proof store.
    fn settle(&mut self, pair: Pair, proof: ProofId) -> bool {
        let alternatives = self.settled.entry(pair).or_default();
        if alternatives
            .first()
            .is_some_and(|best| self.agenda.proofs[*best].cost < self.agenda.proofs[proof].cost)
            || alternatives.len() >= self.agenda.limit
        {
            return false;
        }
        alternatives.push(proof);
        self.outgoing[pair.0].insert(pair.1);
        self.incoming[pair.1].insert(pair.0);
        true
    }

    /// Offer all consequences of a newly settled witness in a fixed rule order.
    fn derive(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        self.lift_collections(pair, proof)?;
        self.restrict_input(pair, proof)?;
        self.extend_sums(pair, proof)?;
        self.compose(pair, proof)?;
        self.fanout(pair, proof)
    }

    /// Lift an element-level witness into each indexed collection context.
    fn lift_collections(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        if let Some(lifts) = self.rules.lifts.get(&pair) {
            for &(target, rule) in lifts {
                self.agenda.infer(target, rule, vec![proof], self.types)?;
            }
        }
        Ok(())
    }

    /// Adapt the witness to every indexed narrower input contract.
    fn restrict_input(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        for &source in &self.rules.restrictions[pair.0] {
            self.agenda.infer(
                (source, pair.1),
                Rule::RestrictInput,
                vec![proof],
                self.types,
            )?;
        }
        Ok(())
    }

    /// Carry unhandled sum alternatives alongside the witness output.
    /// Normalization may intern a type, but only admitted outputs produce candidates.
    fn extend_sums(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        let (input, output) = (self.universe.members[pair.0], self.universe.members[pair.1]);
        for &source in &self.rules.sums[pair.0] {
            let variants = self.types.source_variants(self.universe.members[source]);
            let handled = self.types.handled_variants(input);
            let result = self.types.union(
                std::iter::once(output)
                    .chain(variants.difference(&handled).copied())
                    .collect(),
            );
            if let Some(target) = self.universe.members.get_index_of(&result) {
                self.agenda
                    .infer((source, target), Rule::ExtendSum, vec![proof], self.types)?;
            }
        }
        Ok(())
    }

    /// Compose with settled successors and predecessors, so either arrival order works.
    fn compose(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        let (input, output) = pair;
        for &target in &self.outgoing[output] {
            for &next in &self.settled[&(output, target)] {
                self.agenda.infer(
                    (input, target),
                    Rule::Compose,
                    vec![proof, next],
                    self.types,
                )?;
            }
        }
        for &source in &self.incoming[input] {
            for &previous in &self.settled[&(source, input)] {
                self.agenda.infer(
                    (source, output),
                    Rule::Compose,
                    vec![previous, proof],
                    self.types,
                )?;
            }
        }
        Ok(())
    }

    /// Pair witnesses sharing an input, considering both orders of the output product.
    fn fanout(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        let (input, output) = pair;
        for &other_output in &self.outgoing[input] {
            for &other in &self.settled[&(input, other_output)] {
                for (outputs, children) in [
                    ((output, other_output), [proof, other]),
                    ((other_output, output), [other, proof]),
                ] {
                    if let Some(&target) = self.rules.fanouts.get(&outputs) {
                        self.agenda.infer(
                            (input, target),
                            Rule::Fanout,
                            children.to_vec(),
                            self.types,
                        )?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Independently check each reported witness and diagnose goals with no derivation.
    /// Reachable outputs are sampled in discovery order from the settled relation.
    fn check_features(
        &self,
        primitives: &[Primitive],
        features: &[Primitive],
    ) -> Result<Vec<FeatureStatus>, String> {
        features
            .iter()
            .map(|feature| {
                let goal = self.universe.pair(feature.input, feature.output);
                match self.settled.get(&goal) {
                    Some(witnesses) => {
                        for &proof in witnesses {
                            self.agenda
                                .proofs
                                .check_against(proof, primitives, self.types)?;
                        }
                        Ok(FeatureStatus::Proved {
                            proofs: witnesses.clone(),
                        })
                    }
                    None => {
                        let reachable = self.outgoing[goal.0]
                            .iter()
                            .take(16)
                            .map(|&index| self.universe.members[index])
                            .collect::<Vec<_>>();
                        let reason = failure_reason(feature.output, &reachable, self.types);
                        Ok(FeatureStatus::UnresolvableWithinUniverse { reason, reachable })
                    }
                }
            })
            .collect()
    }
}

/// Build the finite universe, prepare rules, solve goals, and verify the resulting witnesses.
/// Resource or witness-check failures propagate to `search`, which marks the run incomplete.
fn run(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    proofs: &mut ProofStore,
    options: &ValidationOptions,
    tuple_arity: usize,
) -> Result<Vec<FeatureStatus>, String> {
    if features.is_empty() {
        return Ok(Vec::new());
    }
    let mut budget = Budget {
        remaining: options.max_steps.get(),
    };
    let universe = SearchUniverse::build(
        primitives,
        features,
        types,
        options,
        tuple_arity,
        &mut budget,
    )?;
    let mut search = ProofSearch::new(&universe, types, proofs, budget, options.max_proofs.get());
    search.prepare(primitives)?;
    search.solve(features)?;
    search.check_features(primitives, features)
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
