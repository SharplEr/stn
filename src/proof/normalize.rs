//! Conservative equivalence keys for alternative selection, not replacement witnesses.
use super::{Proof, ProofId, ProofNode, Rule};
use crate::{Type, TypeId, TypeStore};
use indexmap::IndexSet;
use std::{collections::HashMap, ops::Index};

/// Index of a canonical composition in one search's normalization store.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct NormalId(usize);

/// A type boundary in an equivalence key. Virtual anonymous sums can occur when
/// distributing an extension; they never add types to the search universe.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Boundary {
    /// Any non-sum type, including a nominal sum whose identity stays opaque here.
    Type(TypeId),
    /// At least two distinct non-sum alternatives, sorted by their store identifiers.
    Sum(Vec<TypeId>),
}

impl Boundary {
    fn from_type(id: TypeId, types: &TypeStore) -> Self {
        match &types[id] {
            Type::Sum(items) => Self::from_variants(items.clone()),
            _ => Self::Type(id),
        }
    }

    fn from_variants(mut variants: Vec<TypeId>) -> Self {
        variants.sort_unstable();
        variants.dedup();
        match variants.as_slice() {
            &[single] => Self::Type(single),
            _ => Self::Sum(variants),
        }
    }

    /// Variants explicitly accepted by this boundary, preserving nominal identity.
    fn handled(&self) -> &[TypeId] {
        match self {
            Self::Type(id) => std::slice::from_ref(id),
            Self::Sum(items) => items,
        }
    }

    /// Inspect a supplied nominal sum only at the boundary of an extension.
    fn supplied(&self, types: &TypeStore) -> Vec<TypeId> {
        match self {
            Self::Type(id) => types.source_variants(*id).into_iter().collect(),
            Self::Sum(items) => items.clone(),
        }
    }

    fn with_variants(&self, variants: &[TypeId]) -> Self {
        Self::from_variants(self.handled().iter().chain(variants).copied().collect())
    }

    fn disjoint(&self, variants: &[TypeId]) -> bool {
        variants
            .iter()
            .all(|id| self.handled().binary_search(id).is_err())
    }
}

/// Typed canonical composition. Costs belong to the original proof, not this key.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) struct NormalForm {
    /// Exact input identity, including nominal wrappers.
    input: Boundary,
    /// Exact output identity, including nominal wrappers.
    output: Boundary,
    /// Operation with references to already normalized premises.
    node: NormalNode,
}

/// Composition structure retained when distinguishing alternatives.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum NormalNode {
    /// Expanded primitive index, distinguishing declarations and generic specializations.
    Primitive(usize),
    /// Ordered, flattened composition with at least two steps.
    Pipeline(Vec<NormalId>),
    /// Every other rule retains its kind, arguments, and ordered premises.
    Inference { rule: Rule, children: Vec<NormalId> },
}

/// Search-local interning of equivalence keys and their accepted proof representatives.
/// Only accepted witnesses are memoized; keys can share subexpressions without
/// copying proof trees or introducing synthetic witnesses into the search.
#[derive(Default)]
pub(crate) struct NormalForms {
    /// Canonical typed expressions, stored once with stable indices.
    nodes: IndexSet<NormalForm>,
    /// Normal form of each accepted witness, whose children precede it in the store.
    witnesses: HashMap<ProofId, NormalId>,
}

impl NormalForms {
    /// Normalize a candidate from previously accepted premises. Associate composition
    /// uniformly and move sum extensions only when their pass-through branches stay inert.
    pub(crate) fn candidate(&mut self, proof: &Proof, types: &TypeStore) -> NormalId {
        let input = Boundary::from_type(proof.input, types);
        let output = Boundary::from_type(proof.output, types);
        let node = match &proof.node {
            ProofNode::Primitive { id, .. } => NormalNode::Primitive(*id),
            ProofNode::Inference { rule, children } => {
                let children = children
                    .iter()
                    .map(|id| self.witnesses[id])
                    .collect::<Vec<_>>();
                match (rule, children.as_slice()) {
                    (Rule::Compose, [_, _]) => return self.pipeline(children),
                    (Rule::ExtendSum, &[child]) => return self.extend(input, child, types),
                    _ => NormalNode::Inference {
                        rule: *rule,
                        children,
                    },
                }
            }
        };
        self.insert(NormalForm {
            input,
            output,
            node,
        })
    }

    /// Associate a retained proof with its key so future candidates reuse its normalization.
    pub(crate) fn remember(&mut self, proof: ProofId, normal: NormalId) {
        self.witnesses.insert(proof, normal);
    }

    fn insert(&mut self, form: NormalForm) -> NormalId {
        NormalId(self.nodes.insert_full(form).0)
    }

    /// Flatten composition at this level only; unary rules and fanout retain scope.
    fn pipeline(&mut self, children: Vec<NormalId>) -> NormalId {
        let mut steps = Vec::new();
        for child in children {
            match &self[child].node {
                NormalNode::Pipeline(inner) => steps.extend_from_slice(inner),
                _ => steps.push(child),
            }
        }
        self.insert(NormalForm {
            input: self[steps[0]].input.clone(),
            output: self[*steps.last().expect("composition has premises")]
                .output
                .clone(),
            node: NormalNode::Pipeline(steps),
        })
    }

    /// Normalize one sum extension. Eliminate an unchanged boundary, fuse nested
    /// extensions through anonymous sums, and distribute over a pipeline only if
    /// every later step leaves the outer pass-through variants untouched.
    fn extend(&mut self, input: Boundary, child: NormalId, types: &TypeStore) -> NormalId {
        if input == self[child].input {
            return child;
        }
        let carried = input
            .supplied(types)
            .into_iter()
            .filter(|id| self[child].input.handled().binary_search(id).is_err())
            .collect::<Vec<_>>();
        match &self[child].node {
            NormalNode::Inference {
                rule: Rule::ExtendSum,
                children,
            } if matches!(self[child].input, Boundary::Sum(_)) => {
                return self.extend(input, children[0], types);
            }
            NormalNode::Pipeline(steps)
                if steps[1..].iter().all(|&step| self.bypasses(step, &carried)) =>
            {
                let steps = steps.clone();
                let mut extended = Vec::with_capacity(steps.len());
                extended.push(self.extend(input, steps[0], types));
                for step in steps.into_iter().skip(1) {
                    let source = self[step].input.with_variants(&carried);
                    extended.push(self.extend(source, step, types));
                }
                return self.pipeline(extended);
            }
            _ => {}
        }
        let output = self[child].output.with_variants(&carried);
        self.insert(NormalForm {
            input,
            output,
            node: NormalNode::Inference {
                rule: Rule::ExtendSum,
                children: vec![child],
            },
        })
    }

    /// An outer carried variant may overlap a later step's input only when that
    /// step is itself an anonymous-sum extension that passes the variant unchanged.
    /// A nominal sum cannot be treated this way: inspecting it consumes its wrapper.
    fn bypasses(&self, step: NormalId, carried: &[TypeId]) -> bool {
        let form = &self[step];
        if form.input.disjoint(carried) {
            return true;
        }
        match &form.node {
            NormalNode::Inference {
                rule: Rule::ExtendSum,
                children,
            } if matches!(form.input, Boundary::Sum(_)) => {
                self[children[0]].input.disjoint(carried)
            }
            _ => false,
        }
    }
}

impl Index<NormalId> for NormalForms {
    type Output = NormalForm;

    fn index(&self, id: NormalId) -> &Self::Output {
        &self.nodes[id.0]
    }
}

#[cfg(test)]
mod tests;
