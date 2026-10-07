//! Resumable generation of the existing relevant and exhaustive type domains.
use super::{Budget, Pair};
use crate::{Type, TypeId, TypeStore, model::Primitive};
use indexmap::IndexSet;
use std::collections::{HashMap, VecDeque};

/// Admitted endpoints with stable identifiers and a suspended domain generator.
pub(super) struct IncrementalUniverse {
    pub members: IndexSet<TypeId>,
    generator: Generator,
}

/// The two domain definitions share admission but have different enumeration tasks.
enum Generator {
    Relevant(RelevantUniverse),
    Exhaustive(ExhaustiveUniverse),
}

impl IncrementalUniverse {
    /// Collect explicit shapes before starting any bounded anonymous synthesis.
    pub fn new(
        primitives: &[Primitive],
        features: &[Primitive],
        types: &mut TypeStore,
        arity: usize,
        budget: &mut Budget<'_>,
    ) -> Result<Self, String> {
        let members = explicit_types(primitives, features, types, budget)?;
        let generator = if budget.options.exhaustive {
            Generator::Exhaustive(ExhaustiveUniverse::new(&members, types, arity))
        } else {
            Generator::Relevant(RelevantUniverse::new(&members, primitives, types, budget)?)
        };
        Ok(Self { members, generator })
    }

    /// Execute a bounded batch and return only newly admitted endpoints for rule activation.
    /// Every cursor advances even when a generated candidate was already present.
    pub fn advance(
        &mut self,
        types: &mut TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<Vec<TypeId>, String> {
        let before = self.members.len();
        match &mut self.generator {
            Generator::Relevant(generator) => {
                for _ in 0..64 {
                    if !generator.advance(&mut self.members, types, budget)? {
                        break;
                    }
                }
            }
            Generator::Exhaustive(generator) => {
                for _ in 0..64 {
                    let Some(ty) = generator.next(&self.members, types, budget)? else {
                        break;
                    };
                    budget.insert_type(&mut self.members, ty)?;
                }
            }
        }
        Ok(self.members.iter().skip(before).copied().collect())
    }

    pub fn is_complete(&self) -> bool {
        match &self.generator {
            Generator::Relevant(generator) => generator.pending.is_empty(),
            Generator::Exhaustive(generator) => matches!(generator.stage, ExhaustiveStage::Done),
        }
    }
}

/// Collect declarations and subexpressions, following each direct nominal body once.
/// Declaration collection may batch allocations; type usage records only admitted capacity.
fn explicit_types(
    primitives: &[Primitive],
    features: &[Primitive],
    types: &mut TypeStore,
    budget: &mut Budget<'_>,
) -> Result<IndexSet<TypeId>, String> {
    let mut out = IndexSet::new();
    for p in primitives.iter().chain(features) {
        types.collect(p.input, &mut out);
        types.collect(p.output, &mut out);
    }
    let declarations = types.collect_declarations(&mut out, budget.options.max_types.get());
    budget.record_types(out.len());
    declarations?;
    let mut next = 0;
    while next < out.len() {
        let ty = out[next];
        next += 1;
        types.collect(types.shape(ty), &mut out);
        budget.record_types(out.len());
        if out.len() > budget.options.max_types.get() {
            return Err("explicit types exceed --max-types".into());
        }
    }
    out.sort_unstable_by(|a, b| types.compare(*a, *b));
    Ok(out)
}

/// A join cursor covers a fixed snapshot; later additions schedule their own delta joins.
enum RelevantTask {
    Step {
        step: Pair,
        next: usize,
        end: usize,
    },
    Context {
        source: TypeId,
        next: usize,
        end: usize,
    },
    NarrowSource {
        source: TypeId,
        next: usize,
        end: usize,
    },
    NarrowTarget {
        target: TypeId,
        next: usize,
        end: usize,
    },
}

/// Elementary closure, independent of the general proof relation and its derived morphisms.
struct RelevantUniverse {
    explicit: IndexSet<TypeId>,
    steps: IndexSet<Pair>,
    contexts: Vec<TypeId>,
    collections: Vec<TypeId>,
    nominal_targets: HashMap<TypeId, Vec<TypeId>>,
    pending: VecDeque<RelevantTask>,
}

impl RelevantUniverse {
    /// Seed the same elementary transformations as the eager algorithm. Only sum and
    /// collection contexts can enable synthesis, so atomic types need no context joins.
    fn new(
        explicit: &IndexSet<TypeId>,
        primitives: &[Primitive],
        types: &TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<Self, String> {
        let mut result = Self {
            explicit: explicit.clone(),
            steps: IndexSet::new(),
            contexts: Vec::new(),
            collections: Vec::new(),
            nominal_targets: HashMap::new(),
            pending: VecDeque::new(),
        };
        for &ty in explicit {
            let shape = types.shape(ty);
            if matches!(
                types[shape],
                Type::Sum(_) | Type::List(_) | Type::Set(_) | Type::Map(..)
            ) {
                result.contexts.push(ty);
            }
            if matches!(types[shape], Type::List(_) | Type::Set(_) | Type::Map(..)) {
                result.collections.push(ty);
                result.pending.push_back(RelevantTask::NarrowSource {
                    source: ty,
                    next: 0,
                    end: explicit.len(),
                });
            }
            if matches!(types[ty], Type::Named(..)) {
                result.nominal_targets.entry(shape).or_default().push(ty);
            }
        }
        for &ty in explicit {
            let shape = types.shape(ty);
            if shape != ty {
                result.add_step((ty, shape));
            }
            if let Type::Product(items) = &types[shape] {
                for &item in items {
                    result.add_step((ty, item));
                }
            }
        }
        for p in primitives {
            result.add_step((p.input, p.output));
            for &source in explicit {
                budget.tick()?;
                if types.accepts(p.input, source) {
                    result.add_step((source, p.output));
                }
            }
        }
        Ok(result)
    }

    fn add_step(&mut self, step: Pair) {
        if self.steps.insert(step) && !self.contexts.is_empty() {
            self.pending.push_back(RelevantTask::Step {
                step,
                next: 0,
                end: self.contexts.len(),
            });
        }
    }

    /// Admit a synthesis result and schedule precisely the previously unseen joins.
    fn admit(
        &mut self,
        ty: TypeId,
        known: &mut IndexSet<TypeId>,
        types: &TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<bool, String> {
        if !self.explicit.contains(&ty) && types.depth(ty) > budget.options.max_depth {
            return Ok(false);
        }
        if budget.insert_type(known, ty)? {
            if !self.collections.is_empty() {
                self.pending.push_back(RelevantTask::NarrowTarget {
                    target: ty,
                    next: 0,
                    end: self.collections.len(),
                });
            }
            let shape = types.shape(ty);
            if matches!(
                types[shape],
                Type::Sum(_) | Type::List(_) | Type::Set(_) | Type::Map(..)
            ) {
                self.contexts.push(ty);
                if !self.steps.is_empty() {
                    self.pending.push_back(RelevantTask::Context {
                        source: ty,
                        next: 0,
                        end: self.steps.len(),
                    });
                }
            }
            if matches!(types[shape], Type::List(_) | Type::Set(_) | Type::Map(..)) {
                self.collections.push(ty);
                self.pending.push_back(RelevantTask::NarrowSource {
                    source: ty,
                    next: 0,
                    end: known.len(),
                });
            }
        }
        Ok(true)
    }

    /// A changed nominal collection may retain a declared nominal result identity.
    fn collection_step(
        &mut self,
        source: TypeId,
        node: Type,
        known: &mut IndexSet<TypeId>,
        types: &mut TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<(), String> {
        let target = types.intern(node);
        if self.admit(target, known, types, budget)? {
            if matches!(types[source], Type::Named(..)) && types.shape(source) != target {
                for nominal in self
                    .nominal_targets
                    .get(&target)
                    .cloned()
                    .unwrap_or_default()
                {
                    self.add_step((source, nominal));
                }
            }
            self.add_step((source, target));
        }
        Ok(())
    }

    /// Consume one join and put its remaining range back before executing its consequences.
    fn advance(
        &mut self,
        known: &mut IndexSet<TypeId>,
        types: &mut TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<bool, String> {
        let Some(task) = self.pending.pop_front() else {
            return Ok(false);
        };
        budget.tick()?;
        match task {
            RelevantTask::Step { step, next, end } => {
                if next + 1 < end {
                    self.pending.push_front(RelevantTask::Step {
                        step,
                        next: next + 1,
                        end,
                    });
                }
                self.apply(step, self.contexts[next], known, types, budget)?;
            }
            RelevantTask::Context { source, next, end } => {
                if next + 1 < end {
                    self.pending.push_front(RelevantTask::Context {
                        source,
                        next: next + 1,
                        end,
                    });
                }
                self.apply(self.steps[next], source, known, types, budget)?;
            }
            RelevantTask::NarrowSource { source, next, end } => {
                if next + 1 < end {
                    self.pending.push_front(RelevantTask::NarrowSource {
                        source,
                        next: next + 1,
                        end,
                    });
                }
                self.narrow(source, known[next], known, types, budget)?;
            }
            RelevantTask::NarrowTarget { target, next, end } => {
                if next + 1 < end {
                    self.pending.push_front(RelevantTask::NarrowTarget {
                        target,
                        next: next + 1,
                        end,
                    });
                }
                self.narrow(self.collections[next], target, known, types, budget)?;
            }
        }
        Ok(true)
    }

    /// Lift one elementary transform through a compatible collection or sum context.
    fn apply(
        &mut self,
        (a, b): Pair,
        source: TypeId,
        known: &mut IndexSet<TypeId>,
        types: &mut TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<(), String> {
        let handled = types.handled_variants(a);
        let variants = types.source_variants(source);
        if source != a && handled.is_subset(&variants) {
            let target = types.union(
                std::iter::once(b)
                    .chain(variants.difference(&handled).copied())
                    .collect(),
            );
            if self.admit(target, known, types, budget)? {
                self.add_step((source, target));
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
            self.collection_step(source, node, known, types, budget)?;
        }
        Ok(())
    }

    /// Narrow towards the same available alternatives as the original relevant closure.
    fn narrow(
        &mut self,
        source: TypeId,
        target: TypeId,
        known: &mut IndexSet<TypeId>,
        types: &mut TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<(), String> {
        let shape = types.shape(source);
        let (item, node) = match types[shape] {
            Type::List(item) => (item, Type::List(target)),
            Type::Set(item) => (item, Type::Set(target)),
            Type::Map(key, value) => (key, Type::Map(target, value)),
            _ => unreachable!("only collection sources are scheduled"),
        };
        if types
            .source_variants(target)
            .is_subset(&types.source_variants(item))
        {
            self.collection_step(source, node, known, types, budget)?;
        }
        Ok(())
    }
}

/// Powerset cursor retaining only normalized sums already encountered, without bit-width limits.
struct SumCursor {
    candidates: Vec<TypeId>,
    sums: IndexSet<TypeId>,
    atom: usize,
    next: usize,
    end: usize,
}
impl SumCursor {
    fn new(candidates: Vec<TypeId>) -> Self {
        Self {
            candidates,
            sums: IndexSet::new(),
            atom: 0,
            next: 0,
            end: 0,
        }
    }
    fn next(&mut self, types: &mut TypeStore) -> Option<TypeId> {
        let &atom = self.candidates.get(self.atom)?;
        let sum = if self.next == 0 {
            atom
        } else {
            types.union(vec![self.sums[self.next - 1], atom])
        };
        self.sums.insert(sum);
        self.next += 1;
        if self.next > self.end {
            self.atom += 1;
            self.next = 0;
            self.end = self.sums.len();
        }
        Some(sum)
    }
}

/// Cartesian constructor cursor: List, Set, Map, then products of each permitted width.
struct ConstructorCursor {
    inner: Vec<TypeId>,
    kind: usize,
    indices: Vec<usize>,
    arity: usize,
}
impl ConstructorCursor {
    fn new(inner: Vec<TypeId>, arity: usize) -> Self {
        Self {
            inner,
            kind: 0,
            indices: vec![0],
            arity,
        }
    }
    fn next(&mut self) -> Option<Type> {
        if self.inner.is_empty() || self.kind > self.arity + 1 {
            return None;
        }
        let node = match self.kind {
            0 => Type::List(self.inner[self.indices[0]]),
            1 => Type::Set(self.inner[self.indices[0]]),
            2 => Type::Map(self.inner[self.indices[0]], self.inner[self.indices[1]]),
            _ => Type::Product(self.indices.iter().map(|&i| self.inner[i]).collect()),
        };
        for index in self.indices.iter_mut().rev() {
            *index += 1;
            if *index < self.inner.len() {
                return Some(node);
            }
            *index = 0;
        }
        self.kind += 1;
        self.indices = vec![
            0;
            match self.kind {
                0 | 1 => 1,
                2 => 2,
                k => k - 1,
            }
        ];
        Some(node)
    }
}

/// Current exhaustive grammar layer; each layer finishes before constructing the next.
enum ExhaustiveStage {
    Unit,
    Sums(SumCursor),
    Constructors(ConstructorCursor),
    Done,
}

/// Lazy depth-layer enumeration with the same explicit exceptions and atom set as before.
struct ExhaustiveUniverse {
    atoms: Vec<TypeId>,
    depth: usize,
    arity: usize,
    stage: ExhaustiveStage,
}
impl ExhaustiveUniverse {
    fn new(explicit: &IndexSet<TypeId>, types: &TypeStore, arity: usize) -> Self {
        Self {
            atoms: explicit
                .iter()
                .copied()
                .filter(|t| matches!(types[*t], Type::Named(..) | Type::Exists(..) | Type::Unit))
                .collect(),
            depth: 0,
            arity,
            stage: ExhaustiveStage::Unit,
        }
    }

    /// Yield one constructor candidate, advancing finished layers without allocating their products.
    fn next(
        &mut self,
        known: &IndexSet<TypeId>,
        types: &mut TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<Option<TypeId>, String> {
        loop {
            if matches!(self.stage, ExhaustiveStage::Done) {
                return Ok(None);
            }
            budget.tick()?;
            match &mut self.stage {
                ExhaustiveStage::Unit => {
                    let unit = types.intern(Type::Unit);
                    if !self.atoms.contains(&unit) {
                        self.atoms.push(unit);
                    }
                    self.stage =
                        ExhaustiveStage::Sums(SumCursor::new(std::mem::take(&mut self.atoms)));
                    return Ok(Some(unit));
                }
                ExhaustiveStage::Sums(cursor) => {
                    if let Some(ty) = cursor.next(types) {
                        return Ok(Some(ty));
                    }
                    self.depth += 1;
                    self.stage = if self.depth > budget.options.max_depth {
                        ExhaustiveStage::Done
                    } else {
                        let inner = known
                            .iter()
                            .copied()
                            .filter(|t| types.depth(*t) < self.depth)
                            .collect();
                        ExhaustiveStage::Constructors(ConstructorCursor::new(inner, self.arity))
                    };
                }
                ExhaustiveStage::Constructors(cursor) => {
                    if let Some(node) = cursor.next() {
                        return Ok(Some(types.intern(node)));
                    }
                    let candidates = known
                        .iter()
                        .copied()
                        .filter(|t| {
                            !matches!(types[*t], Type::Sum(_)) && types.depth(*t) <= self.depth
                        })
                        .collect();
                    self.stage = ExhaustiveStage::Sums(SumCursor::new(candidates));
                }
                ExhaustiveStage::Done => unreachable!(),
            }
        }
    }
}
