//! Conservative full-domain lower bounds, independent of concrete type generation.
use super::{Budget, Pair};
use crate::{Type, TypeId, TypeStore, model::Primitive, proof::Cost};
use indexmap::IndexSet;
use std::{
    cmp::Reverse,
    collections::{BinaryHeap, HashMap},
};

/// A primitive in the product/opaque-type relaxation: shared prerequisites combine by maximum.
struct RelaxedPrimitive {
    inputs: Vec<TypeId>,
    outputs: Vec<TypeId>,
}

/// An optimistic capability model for the closed first-order relevant fragment.
/// Products expose all their components for free, including nominal product views.
/// This permits sharing and forgets nominal construction constraints, so it can only lower cost.
struct RelaxedModel {
    components: HashMap<TypeId, Vec<TypeId>>,
    primitives: Vec<RelaxedPrimitive>,
    dependents: HashMap<TypeId, Vec<usize>>,
}

/// Compute one bound per distinct ground goal; repeated goals do not repeat heuristic work.
/// All other fragments, including exhaustive anonymous construction, use the universal (0,1).
/// Every proof either contains a primitive or at least one inference, so that fallback is safe.
pub(super) fn lower_bounds(
    goals: &[Pair],
    explicit: &IndexSet<TypeId>,
    primitives: &[Primitive],
    types: &TypeStore,
    budget: &mut Budget<'_>,
) -> Result<HashMap<Pair, Cost>, String> {
    let mut bounds = goals
        .iter()
        .map(|&goal| {
            (goal, Cost {
                functions: 0,
                rules: 1,
            })
        })
        .collect::<HashMap<_, _>>();
    // A single unsupported declaration disables positive bounds for the whole domain:
    // it could enable an indirect cheaper path even for an apparently simple goal.
    if budget.options.exhaustive
        || explicit
            .iter()
            .any(|t| !matches!(types[*t], Type::Named(..) | Type::Product(_) | Type::Unit))
    {
        return Ok(bounds);
    }
    let model = RelaxedModel::build(explicit, primitives, types, budget)?;
    let sources = goals.iter().map(|g| g.0).collect::<IndexSet<_>>();
    for source in sources {
        let costs = model.costs(source, budget)?;
        for &(input, output) in goals {
            if input != source {
                continue;
            }
            let count = model.components[&output]
                .iter()
                .map(|atom| costs.get(atom).copied())
                .collect::<Option<Vec<_>>>();
            if let Some(count) = count {
                let functions = count.into_iter().max().unwrap_or(0);
                let rules = if functions == 0 { 1 } else { functions - 1 };
                bounds.insert((input, output), Cost { functions, rules });
            }
        }
    }
    Ok(bounds)
}

impl RelaxedModel {
    /// Flatten nominal views and products. Declaration cycles were rejected during elaboration.
    fn components(
        ty: TypeId,
        types: &TypeStore,
        cache: &mut HashMap<TypeId, Vec<TypeId>>,
    ) -> Vec<TypeId> {
        if let Some(items) = cache.get(&ty) {
            return items.clone();
        }
        let shape = types.shape(ty);
        let items = if shape != ty {
            Self::components(shape, types, cache)
        } else if let Type::Product(items) = &types[ty] {
            items
                .iter()
                .flat_map(|t| Self::components(*t, types, cache))
                .collect::<IndexSet<_>>()
                .into_iter()
                .collect()
        } else {
            vec![ty]
        };
        cache.insert(ty, items.clone());
        items
    }

    /// Compile primitive prerequisite incidence lists once for all feature inputs.
    fn build(
        explicit: &IndexSet<TypeId>,
        primitives: &[Primitive],
        types: &TypeStore,
        budget: &mut Budget<'_>,
    ) -> Result<Self, String> {
        let mut components = HashMap::new();
        for &ty in explicit {
            budget.tick()?;
            Self::components(ty, types, &mut components);
        }
        let mut dependents = HashMap::<_, Vec<_>>::new();
        let primitives = primitives
            .iter()
            .enumerate()
            .map(|(id, p)| {
                let inputs = components[&p.input].clone();
                for &input in &inputs {
                    dependents.entry(input).or_default().push(id);
                }
                RelaxedPrimitive {
                    inputs,
                    outputs: components[&p.output].clone(),
                }
            })
            .collect();
        Ok(Self {
            components,
            primitives,
            dependents,
        })
    }

    /// Propagate h_max labels only through primitives affected by a changed prerequisite.
    /// Each output receives 1 + max(input labels); unknown prerequisites defer that primitive.
    fn costs(
        &self,
        source: TypeId,
        budget: &mut Budget<'_>,
    ) -> Result<HashMap<TypeId, usize>, String> {
        let mut costs = HashMap::new();
        let mut queue = BinaryHeap::new();
        for &atom in &self.components[&source] {
            costs.insert(atom, 0);
            queue.push(Reverse((0, atom)));
        }
        while let Some(Reverse((cost, atom))) = queue.pop() {
            budget.tick()?;
            if costs[&atom] != cost {
                continue;
            }
            for &id in self.dependents.get(&atom).into_iter().flatten() {
                budget.tick()?;
                let p = &self.primitives[id];
                let inputs = p
                    .inputs
                    .iter()
                    .map(|t| costs.get(t).copied())
                    .collect::<Option<Vec<_>>>();
                let Some(inputs) = inputs else {
                    continue;
                };
                let next = 1 + inputs.into_iter().max().unwrap_or(0);
                for &output in &p.outputs {
                    if costs.get(&output).is_none_or(|old| next < *old) {
                        costs.insert(output, next);
                        queue.push(Reverse((next, output)));
                    }
                }
            }
        }
        Ok(costs)
    }
}
