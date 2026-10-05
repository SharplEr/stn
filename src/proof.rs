//! Typed proof witnesses and a checker independent of the search agenda.
use crate::Type;
use crate::model::{self, Primitive, TypeInfo};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
};

/// Lexicographic simplicity: occurrences of primitives, then inference nodes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd)]
pub struct Cost {
    /// Number of user-function occurrences in the unfolded proof tree.
    pub functions: usize,
    /// Number of inference-rule occurrences in the unfolded proof tree.
    pub rules: usize,
}

/// Inference operation recorded by a proof node.
/// Rule premises depend on the node's endpoints and ordered child proofs.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum Rule {
    /// Return the logical input with the same semantic type.
    Identity,
    /// Extract a product component at a zero-based index; displayed as one-based.
    Project(usize),
    /// Expose a nominal type's direct structural description in one direction.
    View,
    /// Keep list elements belonging to the target alternatives.
    NarrowList,
    /// Keep set elements belonging to the target alternatives.
    NarrowSet,
    /// Keep map entries whose keys belong to the target alternatives.
    NarrowKeys,
    /// Adapt a morphism to an input accepted by its wider input contract.
    RestrictInput,
    /// Apply a child morphism to handled sum alternatives and preserve the rest.
    ExtendSum,
    /// Apply an element morphism throughout a list.
    MapList,
    /// Apply an element morphism to the image of a set.
    MapSet,
    /// Transform map values while retaining their keys.
    MapValues,
    /// Apply a list-returning element morphism and concatenate its results.
    FlatMap,
    /// Run the left child followed by the right child through a matching type.
    Compose,
    /// Obtain both child results from one logical input as an ordered binary product.
    Fanout,
}
impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Identity => "id",
            Self::Project(i) => return write!(f, "project[{}]", i + 1),
            Self::View => "view",
            Self::NarrowList => "narrowList",
            Self::NarrowSet => "narrowSet",
            Self::NarrowKeys => "narrowKeys",
            Self::RestrictInput => "restrictInput",
            Self::ExtendSum => "extendSum",
            Self::MapList => "mapList",
            Self::MapSet => "mapSet",
            Self::MapValues => "mapValues",
            Self::FlatMap => "flatMap",
            Self::Compose => "compose",
            Self::Fanout => "fanout",
        };
        f.write_str(text)
    }
}

/// Evidence for a single step: a source morphism or an inference application.
/// Inference children are ordered and shared with `Arc`; checking verifies their
/// number, endpoint types, and rule-specific premises.
#[derive(Clone, Debug)]
pub enum ProofNode {
    /// One ground specialization of a morphism declared in `DEFINITIONS`.
    Primitive {
        /// Index in the specification's expanded primitive signature vector.
        id: usize,
        /// Original qualified name of the source morphism.
        name: String,
        /// One-based declaration line used to identify the source contract.
        line: usize,
        /// Preserved semantic description of the source morphism.
        description: String,
        /// Concrete choices for its finite declaration and trait parameters.
        substitutions: BTreeMap<String, Type>,
    },
    /// A structural step justified by zero, one, or two child proofs.
    Inference {
        /// Inference operation whose premises the checker must validate.
        rule: Rule,
        /// Ordered premises; composition uses execution order and fanout uses tuple order.
        children: Vec<Arc<Proof>>,
    },
}

/// Typed witness of a morphism from `input` to `output`, with its simplicity cost.
/// Storage can form a shared DAG, but cost counts the unfolded tree's occurrences.
/// Construction by search is followed by an independent semantic witness check.
#[derive(Clone, Debug)]
pub struct Proof {
    /// Exact semantic input accepted by this proof node.
    pub input: Type,
    /// Exact semantic output established by this proof node.
    pub output: Type,
    /// Lexicographic cost including the node and all child occurrences.
    pub cost: Cost,
    /// Primitive reference or inference step justifying the endpoints.
    pub node: ProofNode,
}
impl Proof {
    pub(crate) fn primitive(id: usize, p: &Primitive) -> Arc<Self> {
        Arc::new(Self {
            input: p.input.clone(),
            output: p.output.clone(),
            cost: Cost {
                functions: 1,
                rules: 0,
            },
            node: ProofNode::Primitive {
                id,
                name: p.name.clone(),
                line: p.line,
                description: p.description.clone(),
                substitutions: p.substitutions.clone(),
            },
        })
    }
    pub(crate) fn inference(
        input: Type,
        output: Type,
        rule: Rule,
        children: Vec<Arc<Self>>,
    ) -> Arc<Self> {
        let mut cost = Cost {
            functions: 0,
            rules: 1,
        };
        for child in &children {
            cost.functions += child.cost.functions;
            cost.rules += child.cost.rules;
        }
        Arc::new(Self {
            input,
            output,
            cost,
            node: ProofNode::Inference { rule, children },
        })
    }
    /// Includes endpoints and primitive source locations, so overloaded names
    /// and different typed rule instances cannot collapse into one alternative.
    pub fn expression(&self) -> String {
        match &self.node {
            ProofNode::Primitive {
                name,
                line,
                substitutions,
                ..
            } => {
                let args = if substitutions.is_empty() {
                    String::new()
                } else {
                    format!(
                        "<{}>",
                        substitutions
                            .iter()
                            .map(|(n, t)| format!("{n}={t}"))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                format!("{name}{args}@{line}[{} -> {}]", self.input, self.output)
            }
            ProofNode::Inference { rule, children } => {
                let args = children
                    .iter()
                    .map(|p| p.expression())
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{rule}[{} -> {}]({args})", self.input, self.output)
            }
        }
    }
}

pub(crate) fn collection_target_allowed(source: &Type, target: &Type, a: &Type, b: &Type) -> bool {
    if !matches!(target, Type::Named(_, _)) {
        return true;
    }
    matches!(source, Type::Named(_, _)) && (a != b || source == target)
}

pub(crate) fn seed_valid(
    rule: Rule,
    a: &Type,
    b: &Type,
    types: &BTreeMap<String, TypeInfo>,
) -> bool {
    let sa = model::explicit_shape(a, types);
    let sb = model::explicit_shape(b, types);
    match rule {
        Rule::Identity => a == b,
        Rule::View => matches!(a, Type::Named(_, _)) && a != &sa && b == &sa,
        Rule::Project(i) => matches!(&sa,Type::Product(v) if v.get(i) == Some(b)),
        Rule::NarrowList | Rule::NarrowSet | Rule::NarrowKeys => {
            let pair = match (rule, &sa, &sb) {
                (Rule::NarrowList, Type::List(s), Type::List(t))
                | (Rule::NarrowSet, Type::Set(s), Type::Set(t)) => Some((&**s, &**t)),
                (Rule::NarrowKeys, Type::Map(s, v), Type::Map(t, w)) if v == w => {
                    Some((&**s, &**t))
                }
                _ => None,
            };
            let Some((s, t)) = pair else {
                return false;
            };
            let from = model::source_variants(s, types);
            let to = model::source_variants(t, types);
            // A nominal result must actually filter alternatives, not rebrand
            // an unchanged shape (even if its element has a different name).
            to.is_subset(&from)
                && collection_target_allowed(a, b, &sa, &sb)
                && (!matches!(b, Type::Named(_, _)) || a == b || to.len() < from.len())
        }
        _ => false,
    }
}

pub(crate) fn unary_valid(
    rule: Rule,
    a: &Type,
    b: &Type,
    child: &Proof,
    types: &BTreeMap<String, TypeInfo>,
) -> bool {
    match rule {
        Rule::RestrictInput => b == &child.output && model::accepts(&child.input, a),
        Rule::ExtendSum => {
            let supplied = model::source_variants(a, types);
            let handled = model::handled_variants(&child.input);
            handled.is_subset(&supplied)
                && b == &model::union_type(
                    std::iter::once(child.output.clone())
                        .chain(supplied.difference(&handled).cloned())
                        .collect(),
                )
        }
        Rule::MapList | Rule::MapSet | Rule::MapValues | Rule::FlatMap => {
            let sa = model::explicit_shape(a, types);
            let sb = model::explicit_shape(b, types);
            let matches = match (rule, &sa, &sb) {
                (Rule::MapList, Type::List(s), Type::List(t))
                | (Rule::MapSet, Type::Set(s), Type::Set(t)) => {
                    **s == child.input && **t == child.output
                }
                (Rule::MapValues, Type::Map(k, s), Type::Map(l, t)) => {
                    k == l && **s == child.input && **t == child.output
                }
                (Rule::FlatMap, Type::List(s), Type::List(t)) => {
                    **s == child.input && child.output == Type::List(t.clone())
                }
                _ => false,
            };
            matches && collection_target_allowed(a, b, &sa, &sb)
        }
        _ => false,
    }
}

pub(crate) fn check(
    proof: &Arc<Proof>,
    primitives: &[Primitive],
    types: &BTreeMap<String, TypeInfo>,
) -> Result<(), String> {
    fn visit(
        p: &Arc<Proof>,
        primitives: &[Primitive],
        types: &BTreeMap<String, TypeInfo>,
        visited: &mut BTreeSet<usize>,
    ) -> Result<(), String> {
        if !visited.insert(Arc::as_ptr(p) as usize) {
            return Ok(());
        }
        let (valid, cost) = match &p.node {
            ProofNode::Primitive {
                id,
                name,
                line,
                substitutions,
                description,
            } => {
                let valid = primitives.get(*id).is_some_and(|decl| {
                    decl.input == p.input
                        && decl.output == p.output
                        && decl.name == *name
                        && decl.line == *line
                        && decl.substitutions == *substitutions
                        && decl.description == *description
                });
                (valid, Cost {
                    functions: 1,
                    rules: 0,
                })
            }
            ProofNode::Inference { rule, children } => {
                for child in children {
                    visit(child, primitives, types, visited)?;
                }
                let valid = match children.as_slice() {
                    [] => seed_valid(*rule, &p.input, &p.output, types),
                    [c] => unary_valid(*rule, &p.input, &p.output, c, types),
                    [l, r] => match rule {
                        Rule::Compose => {
                            p.input == l.input && l.output == r.input && p.output == r.output
                        }
                        Rule::Fanout => {
                            p.input == l.input
                                && l.input == r.input
                                && p.output
                                    == Type::Product(vec![l.output.clone(), r.output.clone()])
                        }
                        _ => false,
                    },
                    _ => false,
                };
                let cost = children.iter().fold(
                    Cost {
                        functions: 0,
                        rules: 1,
                    },
                    |mut sum, c| {
                        sum.functions += c.cost.functions;
                        sum.rules += c.cost.rules;
                        sum
                    },
                );
                (valid, cost)
            }
        };
        if valid && cost == p.cost {
            Ok(())
        } else {
            Err(format!("invalid proof node: {}", p.expression()))
        }
    }
    visit(proof, primitives, types, &mut BTreeSet::new())
}
