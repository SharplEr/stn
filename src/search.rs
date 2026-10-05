//! A finite type universe and a shortest-path agenda over inference hyperedges.
use crate::{
    FeatureStatus, Type, TypeId, TypeStore, ValidationOptions,
    model::Primitive,
    proof::{self, Cost, Proof, ProofId, ProofStore, Rule},
};
use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap},
};

/// Input/output pair of type identifiers interned in the search universe.
type Pair = (usize, usize);
/// Unary rule instances indexed by their required child morphism's type pair.
/// Each entry lists the resulting pair and the rule that produces it.
type UnaryIndex = BTreeMap<Pair, Vec<(Pair, Rule)>>;

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

fn insert_type(
    known: &mut BTreeSet<TypeId>,
    ty: TypeId,
    options: &ValidationOptions,
) -> Result<bool, String> {
    if known.contains(&ty) {
        return Ok(false);
    }
    if known.len() >= options.max_types {
        return Err(format!(
            "type limit ({}) reached; increase --max-types",
            options.max_types
        ));
    }
    known.insert(ty);
    Ok(true)
}

fn explicit_types(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    options: &ValidationOptions,
) -> Result<BTreeSet<TypeId>, String> {
    let mut out = BTreeSet::new();
    for p in primitives.iter().chain(features) {
        types.collect(p.input, &mut out);
        types.collect(p.output, &mut out);
    }
    types.collect_declarations(&mut out, options.max_types)?;
    // Include direct nominal bodies recursively, including predefined Bytes.
    loop {
        let before = out.len();
        for t in out.clone() {
            types.collect(types.shape(t), &mut out);
        }
        if out.len() > options.max_types {
            return Err("explicit types exceed --max-types".into());
        }
        if before == out.len() {
            break;
        }
    }
    Ok(out)
}

fn structural_steps(known: &BTreeSet<TypeId>, types: &TypeStore) -> BTreeSet<(TypeId, TypeId)> {
    let mut steps = BTreeSet::new();
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
fn relevant_universe(
    explicit: &BTreeSet<TypeId>,
    primitives: &[Primitive],
    types: &mut TypeStore,
    options: &ValidationOptions,
    budget: &mut Budget,
) -> Result<BTreeSet<TypeId>, String> {
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
        let mut additions = BTreeSet::new();
        let mut new_steps = BTreeSet::new();
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
                let target = match types[shape] {
                    Type::List(t) if t == a => Some(Type::List(b)),
                    Type::Set(t) if t == a => Some(Type::Set(b)),
                    Type::Map(k, t) if t == a => Some(Type::Map(k, b)),
                    _ => None,
                };
                if let Some(node) = target {
                    let target = types.intern(node);
                    if explicit.contains(&target) || types.depth(target) <= options.max_depth {
                        additions.insert(target);
                        nominal_steps(source, target, &known, types, &mut new_steps);
                        new_steps.insert((source, target));
                    }
                }
                if let (Type::List(t), Type::List(result)) = (&types[shape], &types[b]) {
                    if *t == a {
                        let target = types.intern(Type::List(*result));
                        if explicit.contains(&target) || types.depth(target) <= options.max_depth {
                            additions.insert(target);
                            nominal_steps(source, target, &known, types, &mut new_steps);
                            new_steps.insert((source, target));
                        }
                    }
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
                    let t = types.intern(node);
                    if explicit.contains(&t) || types.depth(t) <= options.max_depth {
                        additions.insert(t);
                        nominal_steps(source, t, &known, types, &mut new_steps);
                        new_steps.insert((source, t));
                    }
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

fn nominal_steps(
    source: TypeId,
    result_shape: TypeId,
    known: &BTreeSet<TypeId>,
    types: &TypeStore,
    steps: &mut BTreeSet<(TypeId, TypeId)>,
) {
    if matches!(types[source], Type::Named(..)) && types.shape(source) != result_shape {
        for &target in known {
            if matches!(types[target], Type::Named(..)) && types.shape(target) == result_shape {
                steps.insert((source, target));
            }
        }
    }
}

fn add_sums(
    known: &mut BTreeSet<TypeId>,
    candidates: &[TypeId],
    types: &mut TypeStore,
    options: &ValidationOptions,
    budget: &mut Budget,
) -> Result<(), String> {
    // Incremental powerset generation has no word-size-dependent bit masks.
    let mut sums = BTreeSet::<TypeId>::new();
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

fn exhaustive_universe(
    explicit: &BTreeSet<TypeId>,
    types: &mut TypeStore,
    options: &ValidationOptions,
    budget: &mut Budget,
    arity: usize,
) -> Result<BTreeSet<TypeId>, String> {
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
struct Agenda {
    /// Maximum distinct alternatives offered at the best cost for each pair.
    limit: usize,
    /// Minimum-cost queue; proof records live exclusively in the proof store.
    heap: BinaryHeap<Reverse<(Cost, ProofId)>>,
    /// Lowest candidate cost offered so far for each input/output type pair.
    best_offered: BTreeMap<Pair, Cost>,
    /// Proof identifiers offered at each pair's best cost, used for deduplication.
    seen: BTreeMap<Pair, BTreeSet<ProofId>>,
}
impl Agenda {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            heap: BinaryHeap::new(),
            best_offered: BTreeMap::new(),
            seen: BTreeMap::new(),
        }
    }
    fn offer(
        &mut self,
        pair: Pair,
        candidate: Proof,
        proofs: &mut ProofStore,
        budget: &mut Budget,
    ) -> Result<(), String> {
        budget.tick()?;
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
        if proofs
            .find(&candidate)
            .is_some_and(|id| alternatives.contains(&id))
        {
            return Ok(());
        }
        let cost = candidate.cost;
        let id = proofs.insert(candidate);
        alternatives.insert(id);
        self.heap.push(Reverse((cost, id)));
        Ok(())
    }
    fn pop(&mut self) -> Option<ProofId> {
        let Reverse((_, id)) = self.heap.pop()?;
        Some(id)
    }
}

pub(crate) fn search(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    options: &ValidationOptions,
    tuple_arity: usize,
) -> (ProofStore, Vec<FeatureStatus>) {
    let mut budget = Budget {
        remaining: options.max_steps,
    };
    let mut proofs = ProofStore::default();
    let mut statuses = match run(
        primitives,
        features,
        types,
        &mut proofs,
        options,
        &mut budget,
        tuple_arity,
    ) {
        Ok(statuses) => statuses,
        Err(message) => features
            .iter()
            .map(|_| FeatureStatus::SearchIncomplete {
                reason: message.clone(),
            })
            .collect(),
    };
    let mut roots = statuses
        .iter()
        .filter_map(|status| match status {
            FeatureStatus::Proved { proofs } => Some(proofs.as_slice()),
            _ => None,
        })
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    proofs.retain_roots(&mut roots);
    let mut roots = roots.into_iter();
    for status in &mut statuses {
        if let FeatureStatus::Proved { proofs } = status {
            for id in proofs {
                *id = roots.next().expect("every reported root was retained");
            }
        }
    }
    (proofs, statuses)
}

fn run(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    proofs: &mut ProofStore,
    options: &ValidationOptions,
    budget: &mut Budget,
    tuple_arity: usize,
) -> Result<Vec<FeatureStatus>, String> {
    if features.is_empty() {
        return Ok(Vec::new());
    }
    let explicit = explicit_types(primitives, features, types, options)?;
    let known = if options.exhaustive {
        exhaustive_universe(&explicit, types, options, budget, tuple_arity)?
    } else {
        relevant_universe(&explicit, primitives, types, options, budget)?
    };
    let mut universe = known.into_iter().collect::<Vec<_>>();
    universe.sort_unstable_by(|a, b| types.compare(*a, *b));
    let ids = universe
        .iter()
        .enumerate()
        .map(|(i, t)| (*t, i))
        .collect::<BTreeMap<_, _>>();
    let mut agenda = Agenda::new(options.max_proofs);
    let mut unary = UnaryIndex::new();
    let mut restrictions = vec![Vec::new(); universe.len()];
    let mut sums = vec![Vec::new(); universe.len()];
    let shapes = universe.iter().map(|t| types.shape(*t)).collect::<Vec<_>>();
    let mut fanouts = BTreeMap::<Pair, usize>::new();
    for (i, &a) in universe.iter().enumerate() {
        agenda.offer(
            (i, i),
            proofs.inference(a, a, Rule::Identity, vec![]),
            proofs,
            budget,
        )?;
        if shapes[i] != a {
            if let Some(&j) = ids.get(&shapes[i]) {
                agenda.offer(
                    (i, j),
                    proofs.inference(a, shapes[i], Rule::View, vec![]),
                    proofs,
                    budget,
                )?;
            }
        }
        if let Type::Product(items) = &types[shapes[i]] {
            for (k, t) in items.iter().enumerate() {
                let j = ids[t];
                agenda.offer(
                    (i, j),
                    proofs.inference(a, *t, Rule::Project(k), vec![]),
                    proofs,
                    budget,
                )?;
            }
        }
        if let Type::Product(items) = &types[a] {
            if let [l, r] = items.as_slice() {
                fanouts.insert((ids[l], ids[r]), i);
            }
        }
        for (j, &b) in universe.iter().enumerate() {
            budget.tick()?;
            if a != b && types.accepts(a, b) {
                restrictions[i].push(j);
            }
            if a != b
                && types
                    .handled_variants(a)
                    .is_subset(&types.source_variants(b))
            {
                sums[i].push(j);
            }
            for rule in [Rule::NarrowList, Rule::NarrowSet, Rule::NarrowKeys] {
                if i != j && proof::seed_valid(rule, a, b, types) {
                    agenda.offer((i, j), proofs.inference(a, b, rule, vec![]), proofs, budget)?;
                }
            }
            if !proof::collection_target_allowed(a, b, shapes[i], shapes[j], types) {
                continue;
            }
            let premise = match (&types[shapes[i]], &types[shapes[j]]) {
                (Type::List(s), Type::List(t)) => Some((s, t, Rule::MapList)),
                (Type::Set(s), Type::Set(t)) => Some((s, t, Rule::MapSet)),
                (Type::Map(k, s), Type::Map(l, t)) if k == l => Some((s, t, Rule::MapValues)),
                _ => None,
            };
            if let Some((s, t, rule)) = premise {
                if let (Some(&l), Some(&r)) = (ids.get(s), ids.get(t)) {
                    unary.entry((l, r)).or_default().push(((i, j), rule));
                }
            }
            if let (Type::List(s), Type::List(_)) = (&types[shapes[i]], &types[shapes[j]]) {
                if let (Some(&l), Some(&r)) = (ids.get(s), ids.get(&shapes[j])) {
                    unary
                        .entry((l, r))
                        .or_default()
                        .push(((i, j), Rule::FlatMap));
                }
            }
        }
    }
    for (id, p) in primitives.iter().enumerate() {
        agenda.offer(
            (ids[&p.input], ids[&p.output]),
            Proof::primitive(id, p),
            proofs,
            budget,
        )?;
    }
    let goals = features
        .iter()
        .map(|f| (ids[&f.input], ids[&f.output]))
        .collect::<Vec<_>>();
    let mut settled = BTreeMap::<Pair, Vec<ProofId>>::new();
    let mut outgoing = vec![BTreeSet::new(); universe.len()];
    let mut incoming = vec![BTreeSet::new(); universe.len()];
    while let Some(p) = agenda.pop() {
        let (input, output, cost) = {
            let node = &proofs[p];
            (node.input, node.output, node.cost)
        };
        budget.tick()?;
        // Every parent costs strictly more than each premise. Once all goals
        // are settled, larger agenda costs cannot yield cheaper alternatives.
        if goals.iter().all(|g| settled.contains_key(g)) {
            let last_goal = goals
                .iter()
                .map(|g| proofs[settled[g][0]].cost)
                .max()
                .unwrap();
            if cost > last_goal {
                break;
            }
        }
        let (a, b) = (ids[&input], ids[&output]);
        let alternatives = settled.entry((a, b)).or_default();
        if alternatives
            .first()
            .is_some_and(|best| proofs[*best].cost < cost)
            || alternatives.len() >= options.max_proofs
        {
            continue;
        }
        alternatives.push(p);
        outgoing[a].insert(b);
        incoming[b].insert(a);
        if let Some(lifts) = unary.get(&(a, b)) {
            for &((s, t), rule) in lifts {
                agenda.offer(
                    (s, t),
                    proofs.inference(universe[s], universe[t], rule, vec![p]),
                    proofs,
                    budget,
                )?;
            }
        }
        for &s in &restrictions[a] {
            agenda.offer(
                (s, b),
                proofs.inference(universe[s], output, Rule::RestrictInput, vec![p]),
                proofs,
                budget,
            )?;
        }
        for &s in &sums[a] {
            let variants = types.source_variants(universe[s]);
            let handled = types.handled_variants(input);
            let result = types.union(
                std::iter::once(output)
                    .chain(variants.difference(&handled).cloned())
                    .collect(),
            );
            if let Some(&t) = ids.get(&result) {
                agenda.offer(
                    (s, t),
                    proofs.inference(universe[s], result, Rule::ExtendSum, vec![p]),
                    proofs,
                    budget,
                )?;
            }
        }
        for &c in &outgoing[b] {
            for &q in &settled[&(b, c)] {
                agenda.offer(
                    (a, c),
                    proofs.inference(input, proofs[q].output, Rule::Compose, vec![p, q]),
                    proofs,
                    budget,
                )?;
            }
        }
        for &x in &incoming[a] {
            for &q in &settled[&(x, a)] {
                agenda.offer(
                    (x, b),
                    proofs.inference(proofs[q].input, output, Rule::Compose, vec![q, p]),
                    proofs,
                    budget,
                )?;
            }
        }
        for &c in &outgoing[a] {
            for &q in &settled[&(a, c)] {
                if let Some(&t) = fanouts.get(&(b, c)) {
                    agenda.offer(
                        (a, t),
                        proofs.inference(input, universe[t], Rule::Fanout, vec![p, q]),
                        proofs,
                        budget,
                    )?;
                }
                if let Some(&t) = fanouts.get(&(c, b)) {
                    agenda.offer(
                        (a, t),
                        proofs.inference(input, universe[t], Rule::Fanout, vec![q, p]),
                        proofs,
                        budget,
                    )?;
                }
            }
        }
    }
    let mut statuses = Vec::new();
    for (feature, &goal) in features.iter().zip(&goals) {
        if let Some(witnesses) = settled.get(&goal) {
            for &p in witnesses {
                proof::check(p, proofs, primitives, types)?;
            }
            statuses.push(FeatureStatus::Proved {
                proofs: witnesses.clone(),
            });
        } else {
            let reachable = outgoing[goal.0]
                .iter()
                .take(16)
                .map(|&t| universe[t])
                .collect::<Vec<_>>();
            let reason = failure_reason(feature.output, &reachable, types);
            statuses.push(FeatureStatus::UnresolvableWithinUniverse { reason, reachable });
        }
    }
    Ok(statuses)
}

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
