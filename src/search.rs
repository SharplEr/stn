//! A finite type universe and a shortest-path agenda over inference hyperedges.
use crate::{
    FeatureStatus, Type, ValidationOptions,
    model::{self, Primitive, TypeInfo},
    proof::{self, Cost, Proof, Rule},
};
use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet, BinaryHeap},
    sync::Arc,
};

type Pair = (usize, usize);
type UnaryIndex = BTreeMap<Pair, Vec<(Pair, Rule)>>;

struct Budget {
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
    known: &mut BTreeSet<Type>,
    ty: Type,
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
    types: &BTreeMap<String, TypeInfo>,
    options: &ValidationOptions,
) -> Result<BTreeSet<Type>, String> {
    let mut out = BTreeSet::new();
    for p in primitives.iter().chain(features) {
        model::collect_type(&p.input, &mut out);
        model::collect_type(&p.output, &mut out);
    }
    for (name, info) in types {
        let envs =
            model::parameter_environments(&info.parameters, types, 0).map_err(|e| e.to_string())?;
        for env in envs {
            let args = info
                .parameters
                .iter()
                .map(|b| env[&b.name].clone())
                .collect();
            let named = Type::Named(name.clone(), args);
            model::collect_type(&named, &mut out);
            model::collect_type(&model::explicit_shape(&named, types), &mut out);
            if out.len() > options.max_types {
                return Err("ground declarations exceed --max-types".into());
            }
        }
    }
    // Resolve all newly discovered nominal bodies (including predefined Bytes).
    loop {
        let before = out.len();
        for t in out.clone() {
            model::collect_type(&model::explicit_shape(&t, types), &mut out);
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

fn structural_steps(
    known: &BTreeSet<Type>,
    types: &BTreeMap<String, TypeInfo>,
) -> BTreeSet<(Type, Type)> {
    let mut steps = BTreeSet::new();
    for t in known {
        let shape = model::explicit_shape(t, types);
        if &shape != t {
            steps.insert((t.clone(), shape.clone()));
        }
        if let Type::Product(items) = shape {
            for item in items {
                steps.insert((t.clone(), item));
            }
        }
    }
    steps
}

/// This profile admits explicit products and closes their existing collection
/// contexts and sums under elementary transformations. It does not claim to
/// enumerate every constructor combination from the exhaustive depth grammar.
fn relevant_universe(
    explicit: &BTreeSet<Type>,
    primitives: &[Primitive],
    types: &BTreeMap<String, TypeInfo>,
    options: &ValidationOptions,
    budget: &mut Budget,
) -> Result<BTreeSet<Type>, String> {
    let mut known = explicit.clone();
    let mut steps = structural_steps(explicit, types);
    steps.extend(
        primitives
            .iter()
            .map(|p| (p.input.clone(), p.output.clone())),
    );
    for primitive in primitives {
        for source in explicit {
            if model::accepts(&primitive.input, source) {
                steps.insert((source.clone(), primitive.output.clone()));
            }
        }
    }
    loop {
        let mut additions = BTreeSet::new();
        let mut new_steps = BTreeSet::new();
        for (a, b) in &steps {
            let handled = model::handled_variants(a);
            for source in &known {
                budget.tick()?;
                let variants = model::source_variants(source, types);
                if source != a && handled.is_subset(&variants) {
                    let target = model::union_type(
                        std::iter::once(b.clone())
                            .chain(variants.difference(&handled).cloned())
                            .collect(),
                    );
                    if explicit.contains(&target) || model::type_depth(&target) <= options.max_depth
                    {
                        additions.insert(target.clone());
                        new_steps.insert((source.clone(), target));
                    }
                }
                let shape = model::explicit_shape(source, types);
                let target = match &shape {
                    Type::List(t) if **t == *a => Some(Type::List(Box::new(b.clone()))),
                    Type::Set(t) if **t == *a => Some(Type::Set(Box::new(b.clone()))),
                    Type::Map(k, t) if **t == *a => Some(Type::Map(k.clone(), Box::new(b.clone()))),
                    _ => None,
                };
                if let Some(target) = target {
                    if explicit.contains(&target) || model::type_depth(&target) <= options.max_depth
                    {
                        additions.insert(target.clone());
                        nominal_steps(source, &target, &known, types, &mut new_steps);
                        new_steps.insert((source.clone(), target));
                    }
                }
                if let (Type::List(t), Type::List(result)) = (&shape, b) {
                    if **t == *a {
                        let target = Type::List(result.clone());
                        if explicit.contains(&target)
                            || model::type_depth(&target) <= options.max_depth
                        {
                            additions.insert(target.clone());
                            nominal_steps(source, &target, &known, types, &mut new_steps);
                            new_steps.insert((source.clone(), target));
                        }
                    }
                }
            }
        }
        // Narrowing can target an explicitly mentioned element type, including
        // the singleton alternatives already collected from each sum.
        for source in &known {
            let shape = model::explicit_shape(source, types);
            for target in &known {
                budget.tick()?;
                let candidate = match &shape {
                    Type::List(item) | Type::Set(item)
                        if model::source_variants(target, types)
                            .is_subset(&model::source_variants(item, types)) =>
                    {
                        Some(if matches!(&shape, Type::List(_)) {
                            Type::List(Box::new(target.clone()))
                        } else {
                            Type::Set(Box::new(target.clone()))
                        })
                    }
                    Type::Map(key, value)
                        if model::source_variants(target, types)
                            .is_subset(&model::source_variants(key, types)) =>
                    {
                        Some(Type::Map(Box::new(target.clone()), value.clone()))
                    }
                    _ => None,
                };
                if let Some(t) = candidate {
                    if explicit.contains(&t) || model::type_depth(&t) <= options.max_depth {
                        additions.insert(t.clone());
                        nominal_steps(source, &t, &known, types, &mut new_steps);
                        new_steps.insert((source.clone(), t));
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
    source: &Type,
    result_shape: &Type,
    known: &BTreeSet<Type>,
    types: &BTreeMap<String, TypeInfo>,
    steps: &mut BTreeSet<(Type, Type)>,
) {
    if matches!(source, Type::Named(_, _)) && model::explicit_shape(source, types) != *result_shape
    {
        for target in known {
            if matches!(target, Type::Named(_, _))
                && model::explicit_shape(target, types) == *result_shape
            {
                steps.insert((source.clone(), target.clone()));
            }
        }
    }
}

fn add_sums(
    known: &mut BTreeSet<Type>,
    candidates: &[Type],
    options: &ValidationOptions,
    budget: &mut Budget,
) -> Result<(), String> {
    // Incremental powerset generation has no word-size-dependent bit masks.
    let mut sums = BTreeSet::<Type>::new();
    for atom in candidates {
        let mut next = vec![atom.clone()];
        for sum in &sums {
            budget.tick()?;
            next.push(model::union_type(vec![sum.clone(), atom.clone()]));
        }
        for sum in next {
            insert_type(known, sum.clone(), options)?;
            sums.insert(sum);
        }
    }
    Ok(())
}

fn exhaustive_universe(
    explicit: &BTreeSet<Type>,
    options: &ValidationOptions,
    budget: &mut Budget,
    arity: usize,
) -> Result<BTreeSet<Type>, String> {
    let mut known = explicit.clone();
    insert_type(&mut known, Type::Unit, options)?;
    let atoms = known
        .iter()
        .filter(|t| matches!(t, Type::Named(_, _) | Type::Exists(_, _, _) | Type::Unit))
        .cloned()
        .collect::<Vec<_>>();
    add_sums(&mut known, &atoms, options, budget)?;
    for depth in 1..=options.max_depth {
        let inner = known
            .iter()
            .filter(|t| model::type_depth(t) < depth)
            .cloned()
            .collect::<Vec<_>>();
        for a in &inner {
            budget.tick()?;
            insert_type(&mut known, Type::List(Box::new(a.clone())), options)?;
            insert_type(&mut known, Type::Set(Box::new(a.clone())), options)?;
            for b in &inner {
                budget.tick()?;
                insert_type(
                    &mut known,
                    Type::Map(Box::new(a.clone()), Box::new(b.clone())),
                    options,
                )?;
            }
        }
        let mut tuples = vec![Vec::new()];
        for width in 1..=arity {
            let mut next = Vec::new();
            for prefix in tuples {
                for t in &inner {
                    budget.tick()?;
                    let mut tuple = prefix.clone();
                    tuple.push(t.clone());
                    if width >= 2 {
                        insert_type(&mut known, Type::Product(tuple.clone()), options)?;
                    }
                    next.push(tuple);
                }
            }
            tuples = next;
        }
        let nonsums = known
            .iter()
            .filter(|t| !matches!(t, Type::Sum(_)) && model::type_depth(t) <= depth)
            .cloned()
            .collect::<Vec<_>>();
        add_sums(&mut known, &nonsums, options, budget)?;
    }
    Ok(known)
}

struct Agenda {
    limit: usize,
    heap: BinaryHeap<Reverse<(Cost, usize)>>,
    pending: BTreeMap<usize, Arc<Proof>>,
    serial: usize,
    best_offered: BTreeMap<Pair, Cost>,
    seen: BTreeMap<Pair, BTreeSet<String>>,
}
impl Agenda {
    fn new(limit: usize) -> Self {
        Self {
            limit,
            heap: BinaryHeap::new(),
            pending: BTreeMap::new(),
            serial: 0,
            best_offered: BTreeMap::new(),
            seen: BTreeMap::new(),
        }
    }
    fn offer(&mut self, pair: Pair, p: Arc<Proof>, budget: &mut Budget) -> Result<(), String> {
        budget.tick()?;
        if self
            .best_offered
            .get(&pair)
            .is_some_and(|best| *best < p.cost)
        {
            return Ok(());
        }
        if self
            .best_offered
            .get(&pair)
            .is_none_or(|best| *best > p.cost)
        {
            self.best_offered.insert(pair, p.cost);
            self.seen.remove(&pair);
        }
        let alternatives = self.seen.entry(pair).or_default();
        if alternatives.len() >= self.limit || !alternatives.insert(p.expression()) {
            return Ok(());
        }
        let id = self.serial;
        self.serial += 1;
        self.heap.push(Reverse((p.cost, id)));
        self.pending.insert(id, p);
        Ok(())
    }
    fn pop(&mut self) -> Option<Arc<Proof>> {
        let Reverse((_, id)) = self.heap.pop()?;
        self.pending.remove(&id)
    }
}

pub(crate) fn search(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &BTreeMap<String, TypeInfo>,
    options: &ValidationOptions,
    tuple_arity: usize,
) -> Vec<FeatureStatus> {
    let mut budget = Budget {
        remaining: options.max_steps,
    };
    let result = run(
        primitives,
        features,
        types,
        options,
        &mut budget,
        tuple_arity,
    );
    match result {
        Ok(statuses) => statuses,
        Err(message) => features
            .iter()
            .map(|_| FeatureStatus::SearchIncomplete {
                reason: message.clone(),
            })
            .collect(),
    }
}

fn run(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &BTreeMap<String, TypeInfo>,
    options: &ValidationOptions,
    budget: &mut Budget,
    tuple_arity: usize,
) -> Result<Vec<FeatureStatus>, String> {
    if features.is_empty() {
        return Ok(Vec::new());
    }
    let explicit = explicit_types(primitives, features, types, options)?;
    let known = if options.exhaustive {
        exhaustive_universe(&explicit, options, budget, tuple_arity)?
    } else {
        relevant_universe(&explicit, primitives, types, options, budget)?
    };
    let universe = known.into_iter().collect::<Vec<_>>();
    let ids = universe
        .iter()
        .enumerate()
        .map(|(i, t)| (t.clone(), i))
        .collect::<BTreeMap<_, _>>();
    let mut agenda = Agenda::new(options.max_proofs);
    let mut unary = UnaryIndex::new();
    let mut restrictions = vec![Vec::new(); universe.len()];
    let mut sums = vec![Vec::new(); universe.len()];
    let shapes = universe
        .iter()
        .map(|t| model::explicit_shape(t, types))
        .collect::<Vec<_>>();
    let mut fanouts = BTreeMap::<Pair, usize>::new();
    for (i, a) in universe.iter().enumerate() {
        agenda.offer(
            (i, i),
            Proof::inference(a.clone(), a.clone(), Rule::Identity, vec![]),
            budget,
        )?;
        if &shapes[i] != a {
            if let Some(&j) = ids.get(&shapes[i]) {
                agenda.offer(
                    (i, j),
                    Proof::inference(a.clone(), shapes[i].clone(), Rule::View, vec![]),
                    budget,
                )?;
            }
        }
        if let Type::Product(items) = &shapes[i] {
            for (k, t) in items.iter().enumerate() {
                let j = ids[t];
                agenda.offer(
                    (i, j),
                    Proof::inference(a.clone(), t.clone(), Rule::Project(k), vec![]),
                    budget,
                )?;
            }
        }
        if let Type::Product(items) = a {
            if let [l, r] = items.as_slice() {
                fanouts.insert((ids[l], ids[r]), i);
            }
        }
        for (j, b) in universe.iter().enumerate() {
            budget.tick()?;
            if a != b && model::accepts(a, b) {
                restrictions[i].push(j);
            }
            if a != b && model::handled_variants(a).is_subset(&model::source_variants(b, types)) {
                sums[i].push(j);
            }
            for rule in [Rule::NarrowList, Rule::NarrowSet, Rule::NarrowKeys] {
                if i != j && proof::seed_valid(rule, a, b, types) {
                    agenda.offer(
                        (i, j),
                        Proof::inference(a.clone(), b.clone(), rule, vec![]),
                        budget,
                    )?;
                }
            }
            if !proof::collection_target_allowed(a, b, &shapes[i], &shapes[j]) {
                continue;
            }
            let premise = match (&shapes[i], &shapes[j]) {
                (Type::List(s), Type::List(t)) => Some((&**s, &**t, Rule::MapList)),
                (Type::Set(s), Type::Set(t)) => Some((&**s, &**t, Rule::MapSet)),
                (Type::Map(k, s), Type::Map(l, t)) if k == l => Some((&**s, &**t, Rule::MapValues)),
                _ => None,
            };
            if let Some((s, t, rule)) = premise {
                if let (Some(&l), Some(&r)) = (ids.get(s), ids.get(t)) {
                    unary.entry((l, r)).or_default().push(((i, j), rule));
                }
            }
            if let (Type::List(s), Type::List(_)) = (&shapes[i], &shapes[j]) {
                if let (Some(&l), Some(&r)) = (ids.get(&**s), ids.get(&shapes[j])) {
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
            budget,
        )?;
    }
    let goals = features
        .iter()
        .map(|f| (ids[&f.input], ids[&f.output]))
        .collect::<Vec<_>>();
    let mut settled = BTreeMap::<Pair, Vec<Arc<Proof>>>::new();
    let mut outgoing = vec![BTreeSet::new(); universe.len()];
    let mut incoming = vec![BTreeSet::new(); universe.len()];
    while let Some(p) = agenda.pop() {
        budget.tick()?;
        // Every parent costs strictly more than each premise. Once all goals
        // are settled, larger agenda costs cannot yield cheaper alternatives.
        if goals.iter().all(|g| settled.contains_key(g)) {
            let last_goal = goals.iter().map(|g| settled[g][0].cost).max().unwrap();
            if p.cost > last_goal {
                break;
            }
        }
        let (a, b) = (ids[&p.input], ids[&p.output]);
        let alternatives = settled.entry((a, b)).or_default();
        if alternatives.first().is_some_and(|best| best.cost < p.cost)
            || alternatives.len() >= options.max_proofs
        {
            continue;
        }
        alternatives.push(p.clone());
        outgoing[a].insert(b);
        incoming[b].insert(a);
        if let Some(lifts) = unary.get(&(a, b)) {
            for &((s, t), rule) in lifts {
                agenda.offer(
                    (s, t),
                    Proof::inference(universe[s].clone(), universe[t].clone(), rule, vec![
                        p.clone(),
                    ]),
                    budget,
                )?;
            }
        }
        for &s in &restrictions[a] {
            agenda.offer(
                (s, b),
                Proof::inference(
                    universe[s].clone(),
                    p.output.clone(),
                    Rule::RestrictInput,
                    vec![p.clone()],
                ),
                budget,
            )?;
        }
        for &s in &sums[a] {
            let variants = model::source_variants(&universe[s], types);
            let handled = model::handled_variants(&p.input);
            let result = model::union_type(
                std::iter::once(p.output.clone())
                    .chain(variants.difference(&handled).cloned())
                    .collect(),
            );
            if let Some(&t) = ids.get(&result) {
                agenda.offer(
                    (s, t),
                    Proof::inference(universe[s].clone(), result, Rule::ExtendSum, vec![
                        p.clone(),
                    ]),
                    budget,
                )?;
            }
        }
        for &c in &outgoing[b] {
            for q in &settled[&(b, c)] {
                agenda.offer(
                    (a, c),
                    Proof::inference(p.input.clone(), q.output.clone(), Rule::Compose, vec![
                        p.clone(),
                        q.clone(),
                    ]),
                    budget,
                )?;
            }
        }
        for &x in &incoming[a] {
            for q in &settled[&(x, a)] {
                agenda.offer(
                    (x, b),
                    Proof::inference(q.input.clone(), p.output.clone(), Rule::Compose, vec![
                        q.clone(),
                        p.clone(),
                    ]),
                    budget,
                )?;
            }
        }
        for &c in &outgoing[a] {
            for q in &settled[&(a, c)] {
                if let Some(&t) = fanouts.get(&(b, c)) {
                    agenda.offer(
                        (a, t),
                        Proof::inference(p.input.clone(), universe[t].clone(), Rule::Fanout, vec![
                            p.clone(),
                            q.clone(),
                        ]),
                        budget,
                    )?;
                }
                if let Some(&t) = fanouts.get(&(c, b)) {
                    agenda.offer(
                        (a, t),
                        Proof::inference(p.input.clone(), universe[t].clone(), Rule::Fanout, vec![
                            q.clone(),
                            p.clone(),
                        ]),
                        budget,
                    )?;
                }
            }
        }
    }
    let mut statuses = Vec::new();
    for (feature, &goal) in features.iter().zip(&goals) {
        if let Some(proofs) = settled.get(&goal) {
            for p in proofs {
                proof::check(p, primitives, types)?;
            }
            statuses.push(FeatureStatus::Proved {
                proofs: proofs.clone(),
            });
        } else {
            let reachable = outgoing[goal.0]
                .iter()
                .take(16)
                .map(|&t| universe[t].clone())
                .collect::<Vec<_>>();
            let reason = failure_reason(&feature.output, &reachable, types);
            statuses.push(FeatureStatus::UnresolvableWithinUniverse { reason, reachable });
        }
    }
    Ok(statuses)
}

fn failure_reason(target: &Type, reachable: &[Type], types: &BTreeMap<String, TypeInfo>) -> String {
    if matches!(target, Type::Named(_, _))
        && reachable
            .iter()
            .any(|t| *t == model::explicit_shape(target, types))
    {
        return format!(
            "the structural shape of {target} is reachable, but no nominal constructor is available; declare a morphism returning {target}"
        );
    }
    if reachable
        .iter()
        .any(|t| matches!(t,Type::Sum(v) if v.contains(target)))
    {
        return format!(
            "a sum containing {target} is reachable; unhandled alternatives cannot be discarded from a scalar result"
        );
    }
    if matches!(target,Type::Product(v) if v.len()>2) {
        return "no path produces the required flat product; fanout creates binary products and does not flatten tuples".into();
    }
    "no derivation reaches the exact output type in the selected universe; declare a missing transformation or name an intermediate type".into()
}
