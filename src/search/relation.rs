//! Incremental inference relationships and a reopenable best-known proof relation.
use super::{Budget, Pair, failure_reason};
use crate::{
    FeatureStatus, Type, TypeId, TypeStore,
    model::Primitive,
    proof::{self, Cost, NormalForms, NormalId, Proof, ProofId, ProofStore, Rule},
};
use indexmap::IndexSet;
use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap, HashSet},
};

/// Pending original witnesses, ordered by cost, with normalization before alternative truncation.
struct Agenda<'a> {
    proofs: &'a mut ProofStore,
    heap: BinaryHeap<Reverse<(Cost, ProofId)>>,
    best: HashMap<Pair, Cost>,
    seen: HashMap<Pair, HashSet<NormalId>>,
    normal_forms: NormalForms,
    limit: usize,
}
impl<'a> Agenda<'a> {
    fn new(proofs: &'a mut ProofStore, limit: usize) -> Self {
        Self {
            proofs,
            heap: BinaryHeap::new(),
            best: HashMap::new(),
            seen: HashMap::new(),
            normal_forms: NormalForms::default(),
            limit,
        }
    }

    /// A cost improvement starts a new revision of a pair's alternatives. Old heap entries
    /// remain immutable evidence but are skipped by cost when popped after an improvement.
    fn offer(
        &mut self,
        candidate: Proof,
        types: &TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<(), String> {
        budget.tick()?;
        let pair = (candidate.input, candidate.output);
        if self
            .best
            .get(&pair)
            .is_some_and(|best| *best < candidate.cost)
        {
            return Ok(());
        }
        if self
            .best
            .get(&pair)
            .is_none_or(|best| *best > candidate.cost)
        {
            self.best.insert(pair, candidate.cost);
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

    fn infer(
        &mut self,
        pair: Pair,
        rule: Rule,
        children: Vec<ProofId>,
        types: &TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<(), String> {
        self.offer(
            self.proofs.inference(pair.0, pair.1, rule, children)?,
            types,
            budget,
        )
    }

    /// A join's representatives all have the same cost. Reject the entire Cartesian
    /// family before constructing witnesses if that cost cannot improve its result pair.
    fn join_can_improve(&self, pair: Pair, left: ProofId, right: ProofId) -> bool {
        let (left, right) = (self.proofs[left].cost, self.proofs[right].cost);
        let cost = Cost {
            functions: left.functions.saturating_add(right.functions),
            rules: left.rules.saturating_add(right.rules).saturating_add(1),
        };
        self.best.get(&pair).is_none_or(|best| {
            cost < *best || (cost == *best && self.seen[&pair].len() < self.limit)
        })
    }
}

/// Indexed endpoints and relationships. The admitted set is the activated prefix of the domain;
/// generated endpoints become usable only after their relationships have been registered.
#[derive(Default)]
struct RuleIndex {
    admitted: IndexSet<TypeId>,
    lifts: HashMap<Pair, Vec<(Pair, Rule)>>,
    restrictions: HashMap<TypeId, Vec<TypeId>>,
    sums: HashMap<TypeId, Vec<TypeId>>,
    fanouts: HashMap<TypeId, Vec<(TypeId, TypeId, bool)>>,
    handled: HashMap<TypeId, IndexSet<TypeId>>,
    supplied: HashMap<TypeId, IndexSet<TypeId>>,
    waiting: HashMap<TypeId, IndexSet<(TypeId, ProofId)>>,
}

/// Live best-known witnesses and their propagation queue. Processing a pair never closes it:
/// a later type or rule can improve it and trigger all its consequences again.
pub(super) struct ProofRelation<'a> {
    pub types: &'a mut TypeStore,
    pub budget: Budget<'a>,
    agenda: Agenda<'a>,
    rules: RuleIndex,
    active: HashMap<Pair, Vec<ProofId>>,
    outgoing: HashMap<TypeId, IndexSet<TypeId>>,
    incoming: HashMap<TypeId, IndexSet<TypeId>>,
}

impl<'a> ProofRelation<'a> {
    pub fn new(types: &'a mut TypeStore, proofs: &'a mut ProofStore, budget: Budget<'a>) -> Self {
        let limit = budget.options.max_proofs.get();
        Self {
            types,
            budget,
            agenda: Agenda::new(proofs, limit),
            rules: RuleIndex::default(),
            active: HashMap::new(),
            outgoing: HashMap::new(),
            incoming: HashMap::new(),
        }
    }

    /// Register each newly admitted endpoint exactly once, considering both ordered pair directions.
    /// Activate new rules against old witnesses before resuming proof propagation.
    pub fn activate(&mut self, additions: &[TypeId]) -> Result<(), String> {
        for &ty in additions {
            if !self.rules.admitted.insert(ty) {
                continue;
            }
            self.rules
                .handled
                .insert(ty, self.types.handled_variants(ty));
            self.rules
                .supplied
                .insert(ty, self.types.source_variants(ty));
            self.seed_structural(ty)?;
            for index in 0..self.rules.admitted.len() {
                let other = self.rules.admitted[index];
                self.activate_pair((ty, other))?;
                if other != ty {
                    self.activate_pair((other, ty))?;
                }
            }
            self.activate_product(ty)?;
            if let Some(waiting) = self.rules.waiting.remove(&ty) {
                for (source, child) in waiting {
                    if self.is_active(child) {
                        self.infer((source, ty), Rule::ExtendSum, vec![child])?;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn seed_primitives(&mut self, primitives: &[Primitive]) -> Result<(), String> {
        for (id, primitive) in primitives.iter().enumerate() {
            self.agenda.offer(
                Proof::primitive(id, primitive),
                self.types,
                &mut self.budget,
            )?;
        }
        Ok(())
    }

    fn infer(&mut self, pair: Pair, rule: Rule, children: Vec<ProofId>) -> Result<(), String> {
        self.agenda
            .infer(pair, rule, children, self.types, &mut self.budget)
    }

    /// Seed identity, directed nominal views, and ordered product projections.
    fn seed_structural(&mut self, source: TypeId) -> Result<(), String> {
        self.infer((source, source), Rule::Identity, vec![])?;
        let shape = self.types.shape(source);
        if source != shape {
            self.infer((source, shape), Rule::View, vec![])?;
        }
        if let Type::Product(items) = &self.types[shape] {
            for (index, target) in items.clone().into_iter().enumerate() {
                self.infer((source, target), Rule::Project(index), vec![])?;
            }
        }
        Ok(())
    }

    /// Add all unary/seed rules for a new endpoint pair and fire them on existing premises.
    fn activate_pair(&mut self, (a, b): Pair) -> Result<(), String> {
        self.budget.tick()?;
        if a != b && self.types.accepts(a, b) {
            self.rules.restrictions.entry(a).or_default().push(b);
            for proof in self.witnesses_from(a) {
                let output = self.agenda.proofs[proof].output;
                self.infer((b, output), Rule::RestrictInput, vec![proof])?;
            }
        }
        if a != b && self.rules.handled[&a].is_subset(&self.rules.supplied[&b]) {
            self.rules.sums.entry(a).or_default().push(b);
            for proof in self.witnesses_from(a) {
                self.extend_at(b, proof)?;
            }
        }
        for rule in [Rule::NarrowList, Rule::NarrowSet, Rule::NarrowKeys] {
            if a != b && proof::seed_valid(rule, a, b, self.types) {
                self.infer((a, b), rule, vec![])?;
            }
        }
        let (sa, sb) = (self.types.shape(a), self.types.shape(b));
        if !proof::collection_target_allowed(a, b, sa, sb, self.types) {
            return Ok(());
        }
        let premise = match (&self.types[sa], &self.types[sb]) {
            (Type::List(s), Type::List(t)) => Some((*s, *t, Rule::MapList)),
            (Type::Set(s), Type::Set(t)) => Some((*s, *t, Rule::MapSet)),
            (Type::Map(k, s), Type::Map(l, t)) if k == l => Some((*s, *t, Rule::MapValues)),
            _ => None,
        };
        if let Some((s, t, rule)) = premise {
            self.activate_lift((s, t), (a, b), rule)?;
        }
        if let (Type::List(s), Type::List(_)) = (&self.types[sa], &self.types[sb]) {
            self.activate_lift((*s, sb), (a, b), Rule::FlatMap)?;
        }
        Ok(())
    }

    fn activate_lift(&mut self, premise: Pair, result: Pair, rule: Rule) -> Result<(), String> {
        self.rules
            .lifts
            .entry(premise)
            .or_default()
            .push((result, rule));
        for proof in self.active.get(&premise).cloned().unwrap_or_default() {
            self.infer(result, rule, vec![proof])?;
        }
        Ok(())
    }

    /// A late product enables fanout even when both branches have already propagated.
    fn activate_product(&mut self, ty: TypeId) -> Result<(), String> {
        let Type::Product(items) = &self.types[ty] else {
            return Ok(());
        };
        let [left, right] = items.as_slice() else {
            return Ok(());
        };
        let (left, right) = (*left, *right);
        self.rules
            .fanouts
            .entry(left)
            .or_default()
            .push((right, ty, false));
        self.rules
            .fanouts
            .entry(right)
            .or_default()
            .push((left, ty, true));
        for source in self.incoming.get(&left).cloned().unwrap_or_default() {
            for l in self.active[&(source, left)].clone() {
                for r in self
                    .active
                    .get(&(source, right))
                    .cloned()
                    .unwrap_or_default()
                {
                    self.infer((source, ty), Rule::Fanout, vec![l, r])?;
                }
            }
        }
        Ok(())
    }

    fn witnesses_from(&self, source: TypeId) -> Vec<ProofId> {
        self.outgoing
            .get(&source)
            .into_iter()
            .flatten()
            .flat_map(|&target| self.active[&(source, target)].iter().copied())
            .collect()
    }

    fn is_active(&self, id: ProofId) -> bool {
        let proof = &self.agenda.proofs[id];
        self.agenda.best.get(&(proof.input, proof.output)) == Some(&proof.cost)
            && self
                .active
                .get(&(proof.input, proof.output))
                .is_some_and(|ids| ids.contains(&id))
    }

    /// Process one candidate. Cost revisions discard stale queued witnesses; improved
    /// active pairs replace their previous alternatives and propagate again.
    pub fn propagate(&mut self) -> Result<bool, String> {
        let Some(Reverse((cost, id))) = self.agenda.heap.pop() else {
            return Ok(false);
        };
        self.budget.tick()?;
        let proof = &self.agenda.proofs[id];
        let pair = (proof.input, proof.output);
        if self.agenda.best[&pair] != cost {
            return Ok(true);
        }
        let alternatives = self.active.entry(pair).or_default();
        if alternatives
            .first()
            .is_some_and(|p| self.agenda.proofs[*p].cost > cost)
        {
            alternatives.clear();
        }
        if alternatives.contains(&id) || alternatives.len() >= self.agenda.limit {
            return Ok(true);
        }
        alternatives.push(id);
        self.outgoing.entry(pair.0).or_default().insert(pair.1);
        self.incoming.entry(pair.1).or_default().insert(pair.0);
        self.derive(pair, id)?;
        Ok(true)
    }

    /// Unary lifts, input adaptation, sum extension, composition, and ordered fanout.
    fn derive(&mut self, pair: Pair, proof: ProofId) -> Result<(), String> {
        for (target, rule) in self.rules.lifts.get(&pair).cloned().unwrap_or_default() {
            self.infer(target, rule, vec![proof])?;
        }
        for source in self
            .rules
            .restrictions
            .get(&pair.0)
            .cloned()
            .unwrap_or_default()
        {
            self.infer((source, pair.1), Rule::RestrictInput, vec![proof])?;
        }
        for source in self.rules.sums.get(&pair.0).cloned().unwrap_or_default() {
            self.extend_at(source, proof)?;
        }
        self.compose(pair, proof)?;
        self.fanout(pair, proof)
    }

    /// Remember an extension whose output is not yet admitted. Later admission fires
    /// it without reprocessing every previously derived morphism or inventing a domain member.
    fn extend_at(&mut self, source: TypeId, child: ProofId) -> Result<(), String> {
        let proof = &self.agenda.proofs[child];
        let variants = self.types.source_variants(source);
        let handled = self.types.handled_variants(proof.input);
        let result = self.types.union(
            std::iter::once(proof.output)
                .chain(variants.difference(&handled).copied())
                .collect(),
        );
        if self.rules.admitted.contains(&result) {
            self.infer((source, result), Rule::ExtendSum, vec![child])?;
        } else {
            self.budget.tick()?;
            self.rules
                .waiting
                .entry(result)
                .or_default()
                .insert((source, child));
        }
        Ok(())
    }

    /// Either arrival order can complete a composition; look up only matching endpoints.
    fn compose(&mut self, (input, output): Pair, proof: ProofId) -> Result<(), String> {
        for target in self.outgoing.get(&output).cloned().unwrap_or_default() {
            self.budget.tick()?;
            let representative = self.active[&(output, target)][0];
            if !self
                .agenda
                .join_can_improve((input, target), proof, representative)
            {
                continue;
            }
            for next in self.active[&(output, target)].clone() {
                self.infer((input, target), Rule::Compose, vec![proof, next])?;
            }
        }
        for source in self.incoming.get(&input).cloned().unwrap_or_default() {
            self.budget.tick()?;
            let representative = self.active[&(source, input)][0];
            if !self
                .agenda
                .join_can_improve((source, output), representative, proof)
            {
                continue;
            }
            for previous in self.active[&(source, input)].clone() {
                self.infer((source, output), Rule::Compose, vec![previous, proof])?;
            }
        }
        Ok(())
    }

    /// Pair same-input branches in both output orders, only for admitted binary products.
    fn fanout(&mut self, (input, output): Pair, proof: ProofId) -> Result<(), String> {
        for (other_output, target, reverse) in
            self.rules.fanouts.get(&output).cloned().unwrap_or_default()
        {
            let Some(others) = self.active.get(&(input, other_output)) else {
                continue;
            };
            self.budget.tick()?;
            if !self
                .agenda
                .join_can_improve((input, target), proof, others[0])
            {
                continue;
            }
            for other in others.clone() {
                let children = if reverse {
                    vec![other, proof]
                } else {
                    vec![proof, other]
                };
                self.infer((input, target), Rule::Fanout, children)?;
            }
        }
        Ok(())
    }

    pub fn cost(&self, goal: Pair) -> Option<Cost> {
        self.active
            .get(&goal)
            .and_then(|p| p.first())
            .map(|p| self.agenda.proofs[*p].cost)
    }

    /// Before domain completion, only work capable of attaining a full-domain lower
    /// bound can finish a goal early. Delay more expensive witnesses until new rules
    /// stop arriving; this avoids propagating paths that late types may improve.
    pub fn can_attain_bound(&self, ceiling: Cost) -> bool {
        self.agenda
            .heap
            .peek()
            .is_some_and(|Reverse((cost, _))| *cost <= ceiling)
    }

    /// Full-domain lower bounds can certify early, but alternatives must also fill the cap.
    pub fn meets_bounds(&self, bounds: &HashMap<Pair, Cost>) -> bool {
        bounds.iter().all(|(goal, bound)| {
            self.cost(*goal) == Some(*bound) && self.active[goal].len() >= self.agenda.limit
        })
    }

    /// With generation/activation finished, positive inference costs exclude all remaining
    /// work once its cost exceeds every goal witness. Missing goals require full saturation.
    pub fn is_saturated_for(&self, goals: &[Pair]) -> bool {
        let Some(Reverse((next, _))) = self.agenda.heap.peek() else {
            return true;
        };
        goals
            .iter()
            .all(|goal| self.cost(*goal).is_some_and(|cost| cost < *next))
    }

    /// Independently check the final roots and produce domain-relative failure diagnostics.
    pub fn check_features(
        &mut self,
        primitives: &[Primitive],
        features: &[Primitive],
    ) -> Result<Vec<FeatureStatus>, String> {
        let roots = features.iter().flat_map(|feature| {
            self.active
                .get(&(feature.input, feature.output))
                .into_iter()
                .flatten()
                .copied()
        });
        self.agenda
            .proofs
            .check_roots(roots, primitives, self.types, || self.budget.tick())?;
        features
            .iter()
            .map(|feature| {
                let goal = (feature.input, feature.output);
                match self.active.get(&goal) {
                    Some(witnesses) => Ok(FeatureStatus::Proved {
                        proofs: witnesses.clone(),
                    }),
                    None => {
                        let reachable = self
                            .outgoing
                            .get(&goal.0)
                            .into_iter()
                            .flatten()
                            .take(16)
                            .copied()
                            .collect::<Vec<_>>();
                        let reason = failure_reason(feature.output, &reachable, self.types);
                        Ok(FeatureStatus::UnresolvableWithinUniverse { reason, reachable })
                    }
                }
            })
            .collect()
    }
}
