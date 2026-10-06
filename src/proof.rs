//! Typed proof witnesses and a checker independent of the search agenda.
use crate::model::Primitive;
use crate::{Type, TypeId, TypeStore, ValidationError, model, syntax};
use indexmap::IndexSet;
use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt,
    ops::Index,
};

/// Lexicographic simplicity: occurrences of primitives, then inference nodes.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Cost {
    /// Number of user-function occurrences in the unfolded proof tree.
    pub functions: usize,
    /// Number of inference-rule occurrences in the unfolded proof tree.
    pub rules: usize,
}

/// Inference operation recorded by a proof node.
/// Rule premises depend on the node's endpoints and ordered child proofs.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
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
/// Inference children are ordered identifiers in the same store; checking verifies their
/// number, endpoint types, and rule-specific premises.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
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
        /// Concrete choices in name order for canonical node hashing and display.
        substitutions: BTreeMap<String, TypeId>,
    },
    /// A structural step justified by zero, one, or two child proofs.
    Inference {
        /// Inference operation whose premises the checker must validate.
        rule: Rule,
        /// Ordered premises; composition uses execution order and fanout uses tuple order.
        children: Vec<ProofId>,
    },
}

/// Typed witness of a morphism from `input` to `output`, with its simplicity cost.
/// Storage can form a shared DAG, but cost counts the unfolded tree's occurrences.
/// Construction by search is followed by an independent semantic witness check.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Proof {
    /// Exact semantic input accepted by this proof node.
    pub input: TypeId,
    /// Exact semantic output established by this proof node.
    pub output: TypeId,
    /// Lexicographic cost including the node and all child occurrences.
    pub cost: Cost,
    /// Primitive reference or inference step justifying the endpoints.
    pub node: ProofNode,
}

/// Index of an immutable proof node in its owning `ProofStore`.
/// Identifiers are cheap to copy and must be used with the store that issued them.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct ProofId(usize);

/// Owner of a proof DAG; nodes refer to shared premises through `ProofId`.
/// Equal records reuse an identifier. The search retains only records reachable
/// from reported roots when it transfers this store into the validation report.
#[derive(Clone, Debug, Default)]
pub struct ProofStore {
    /// Canonical records stored once, with hash lookup and stable insertion indices.
    nodes: IndexSet<Proof>,
}

impl ProofStore {
    /// Number of proof records owned by the store.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the store contains no records.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Look up a record using an identifier originating from this store.
    pub fn get(&self, id: ProofId) -> Option<&Proof> {
        self.nodes.get_index(id.0)
    }

    /// Find an existing record; child identifiers must belong to this store.
    pub fn find(&self, proof: &Proof) -> Option<ProofId> {
        self.nodes.get_index_of(proof).map(ProofId)
    }

    /// Store a record as supplied, reusing an identifier for an equal record.
    /// Children must refer to this store. This does not check inference semantics
    /// or costs; use `Self::check` to validate externally constructed evidence.
    pub fn insert(&mut self, proof: Proof) -> ProofId {
        ProofId(self.nodes.insert_full(proof).0)
    }

    /// Verify an externally stored or modified witness against a specification.
    /// `root` belongs to this store, and `types` owns its type identifiers. Parse
    /// and elaborate the source independently, then translate the witness into
    /// separate stores before checking its rules, source metadata, and costs.
    /// This establishes validity, not minimum cost or compliance with search bounds.
    pub fn check(
        &self,
        root: ProofId,
        source: &str,
        types: &TypeStore,
    ) -> Result<(), ValidationError> {
        let document = syntax::parse(source)?;
        let mut specification = model::elaborate(&document)?;
        let mut imported = Self::default();
        let root = imported
            .import(root, self, types, &mut specification.types)
            .map_err(ValidationError::Invalid)?;
        imported
            .check_against(root, &specification.primitives, &specification.types)
            .map_err(ValidationError::Invalid)
    }

    /// Validate a witness using already resolved declarations in the same type store.
    /// Search uses this entry point without parsing or translating its own graph.
    /// The checker visits shared premises once and rejects cycles and invalid costs.
    pub(crate) fn check_against(
        &self,
        root: ProofId,
        primitives: &[Primitive],
        types: &TypeStore,
    ) -> Result<(), String> {
        ProofChecker {
            proofs: self,
            primitives,
            types,
            visiting: HashSet::new(),
            visited: HashSet::new(),
        }
        .visit(root)
    }

    /// Import a witness from another store, translating all proof and type identifiers.
    /// `root` belongs to `source`; the returned identifier belongs to this store.
    /// Memoization preserves shared premises and visiting marks reject malformed cycles.
    fn import(
        &mut self,
        root: ProofId,
        source: &Self,
        source_types: &TypeStore,
        target_types: &mut TypeStore,
    ) -> Result<ProofId, String> {
        ProofImporter {
            source_types,
            source_proofs: source,
            target_types,
            target_proofs: self,
            types: HashMap::new(),
            proofs: HashMap::new(),
            visiting: HashSet::new(),
        }
        .visit(root)
    }

    /// Build an inference candidate, counting each child occurrence in its cost.
    /// Children must already exist in this store. The candidate is not inserted
    /// here; the agenda first checks its cost and the alternative limit.
    pub(crate) fn inference(
        &self,
        input: TypeId,
        output: TypeId,
        rule: Rule,
        children: Vec<ProofId>,
    ) -> Proof {
        let mut cost = Cost {
            functions: 0,
            rules: 1,
        };
        for &child in &children {
            cost.functions += self[child].cost.functions;
            cost.rules += self[child].cost.rules;
        }
        Proof {
            input,
            output,
            cost,
            node: ProofNode::Inference { rule, children },
        }
    }

    /// Format a well-formed witness, including typed endpoints and source locations.
    /// Shared premises appear at every occurrence in the unfolded expression.
    pub fn expression(&self, id: ProofId, types: &TypeStore) -> String {
        let proof = &self[id];
        match &proof.node {
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
                            .map(|(n, t)| format!("{n}={}", types.display(*t)))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                format!(
                    "{name}{args}@{line}[{} -> {}]",
                    types.display(proof.input),
                    types.display(proof.output)
                )
            }
            ProofNode::Inference { rule, children } => {
                let args = children
                    .iter()
                    .map(|p| self.expression(*p, types))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "{rule}[{} -> {}]({args})",
                    types.display(proof.input),
                    types.display(proof.output)
                )
            }
        }
    }

    /// Keep reported roots and their reachable premises, rebuilding dense indices.
    /// Search-created nodes are topological: all children precede their parents.
    /// Both root identifiers and child references are remapped; all other search
    /// candidates are discarded. Shared premises remain single stored records.
    pub(crate) fn retain_roots(&mut self, roots: &mut [ProofId]) {
        if roots.is_empty() {
            *self = Self::default();
            return;
        }
        let mut marked = vec![false; self.nodes.len()];
        let mut pending = roots.to_vec();
        while let Some(id) = pending.pop() {
            if marked[id.0] {
                continue;
            }
            marked[id.0] = true;
            if let ProofNode::Inference { children, .. } = &self[id].node {
                pending.extend_from_slice(children);
            }
        }
        let old = std::mem::take(self);
        let mut mapping = vec![None; old.nodes.len()];
        // Move surviving records in insertion order, remapping children before parents.
        for (index, mut proof) in old.nodes.into_iter().enumerate() {
            if !marked[index] {
                continue;
            }
            if let ProofNode::Inference { children, .. } = &mut proof.node {
                for child in children {
                    *child = mapping[child.0].expect("search stores children before parents");
                }
            }
            mapping[index] = Some(self.insert(proof));
        }
        for root in roots {
            *root = mapping[root.0].expect("reported root is marked");
        }
    }
}

impl Index<ProofId> for ProofStore {
    type Output = Proof;
    fn index(&self, id: ProofId) -> &Proof {
        &self.nodes[id.0]
    }
}

impl Proof {
    /// Record one expanded user morphism with cost `(1, 0)` and the source
    /// metadata that the independent checker compares against its declaration.
    pub(crate) fn primitive(id: usize, p: &Primitive) -> Self {
        Self {
            input: p.input,
            output: p.output,
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
        }
    }
}

/// Guard collection lifts against implicit nominal construction.
/// An anonymous source cannot acquire a nominal result. A nominal source may
/// produce another nominal collection when the operation changes its shape;
/// preserving a shape only permits preserving the original nominal identity.
pub(crate) fn collection_target_allowed(
    source: TypeId,
    target: TypeId,
    a: TypeId,
    b: TypeId,
    types: &TypeStore,
) -> bool {
    if !matches!(types[target], Type::Named(..)) {
        return true;
    }
    matches!(types[source], Type::Named(..)) && (a != b || source == target)
}

/// Check an inference rule with no child proofs: identity, a directed nominal
/// view, a product projection, or collection narrowing. Other rules return false.
/// Narrowing compares alternative sets while preserving map values. Producing
/// a different nominal collection must remove alternatives, rather than merely
/// rename an unchanged shape. All identifiers must belong to `types`.
pub(crate) fn seed_valid(rule: Rule, a: TypeId, b: TypeId, types: &TypeStore) -> bool {
    let sa = types.shape(a);
    let sb = types.shape(b);
    match rule {
        Rule::Identity => a == b,
        Rule::View => matches!(types[a], Type::Named(..)) && a != sa && b == sa,
        Rule::Project(i) => matches!(&types[sa], Type::Product(v) if v.get(i) == Some(&b)),
        Rule::NarrowList | Rule::NarrowSet | Rule::NarrowKeys => {
            let pair = match (rule, &types[sa], &types[sb]) {
                (Rule::NarrowList, Type::List(s), Type::List(t))
                | (Rule::NarrowSet, Type::Set(s), Type::Set(t)) => Some((*s, *t)),
                (Rule::NarrowKeys, Type::Map(s, v), Type::Map(t, w)) if v == w => Some((*s, *t)),
                _ => None,
            };
            let Some((s, t)) = pair else {
                return false;
            };
            let from = types.source_variants(s);
            let to = types.source_variants(t);
            // A nominal result must actually filter alternatives, not rebrand
            // an unchanged shape (even if its element has a different name).
            to.is_subset(&from)
                && collection_target_allowed(a, b, sa, sb, types)
                && (!matches!(types[b], Type::Named(..)) || a == b || to.len() < from.len())
        }
        _ => false,
    }
}

/// Check the type-level premises of a rule with one child: input restriction,
/// sum extension, a collection lift, or list flattening. Sum extension replaces
/// exactly the handled alternatives and carries every other alternative through.
/// This checks the parent endpoints against the child signature; the caller is
/// responsible for validating the child proof and recomputing the total cost.
pub(crate) fn unary_valid(
    rule: Rule,
    a: TypeId,
    b: TypeId,
    child: &Proof,
    types: &TypeStore,
) -> bool {
    match rule {
        Rule::RestrictInput => b == child.output && types.accepts(child.input, a),
        Rule::ExtendSum => {
            let supplied = types.source_variants(a);
            let handled = types.handled_variants(child.input);
            let expected = types
                .handled_variants(child.output)
                .into_iter()
                .chain(supplied.difference(&handled).copied())
                .collect::<IndexSet<_>>();
            handled.is_subset(&supplied) && types.handled_variants(b) == expected
        }
        Rule::MapList | Rule::MapSet | Rule::MapValues | Rule::FlatMap => {
            let sa = types.shape(a);
            let sb = types.shape(b);
            let matches = match (rule, &types[sa], &types[sb]) {
                (Rule::MapList, Type::List(s), Type::List(t))
                | (Rule::MapSet, Type::Set(s), Type::Set(t)) => {
                    *s == child.input && *t == child.output
                }
                (Rule::MapValues, Type::Map(k, s), Type::Map(l, t)) => {
                    k == l && *s == child.input && *t == child.output
                }
                (Rule::FlatMap, Type::List(s), Type::List(t)) => {
                    *s == child.input
                        && matches!(types[child.output], Type::List(item) if item == *t)
                }
                _ => false,
            };
            matches && collection_target_allowed(a, b, sa, sb, types)
        }
        _ => false,
    }
}

/// State for independently checking one root and its reachable proof DAG.
/// Source graphs stay immutable; active and completed marks belong to this check.
struct ProofChecker<'a> {
    /// Proof graph owning the root and all premise identifiers.
    proofs: &'a ProofStore,
    /// Resolved user morphisms against which primitive metadata is checked.
    primitives: &'a [Primitive],
    /// Type graph shared by proof endpoints and resolved declarations.
    types: &'a TypeStore,
    /// Nodes on the current recursion path, used to reject cycles.
    visiting: HashSet<ProofId>,
    /// Nodes whose rules, source metadata, and unfolded costs have been checked.
    visited: HashSet<ProofId>,
}

impl ProofChecker<'_> {
    /// Check children before their parent, visiting shared premises only once.
    /// Validate rule arity, endpoints, primitive metadata, and checked cost sums.
    fn visit(&mut self, id: ProofId) -> Result<(), String> {
        if self.visited.contains(&id) {
            return Ok(());
        }
        if !self.visiting.insert(id) {
            return Err("proof contains a cycle".into());
        }
        let p = self
            .proofs
            .get(id)
            .ok_or("proof contains an invalid proof identifier")?;
        if self.types.get(p.input).is_none() || self.types.get(p.output).is_none() {
            return Err("proof contains an invalid type identifier".into());
        }
        let (valid, cost) = match &p.node {
            ProofNode::Primitive {
                id,
                name,
                line,
                substitutions,
                description,
            } => {
                let valid = self.primitives.get(*id).is_some_and(|decl| {
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
                for &child in children {
                    self.visit(child)?;
                }
                let valid = match children.as_slice() {
                    [] => seed_valid(*rule, p.input, p.output, self.types),
                    [c] => unary_valid(*rule, p.input, p.output, &self.proofs[*c], self.types),
                    [l, r] => {
                        let l = &self.proofs[*l];
                        let r = &self.proofs[*r];
                        match rule {
                            Rule::Compose => {
                                p.input == l.input && l.output == r.input && p.output == r.output
                            }
                            Rule::Fanout => {
                                p.input == l.input
                                    && l.input == r.input
                                    && matches!(&self.types[p.output], Type::Product(items) if items.as_slice() == [l.output, r.output])
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                };
                let cost = children.iter().try_fold(
                    Cost {
                        functions: 0,
                        rules: 1,
                    },
                    |sum, c| {
                        Ok::<_, String>(Cost {
                            functions: sum
                                .functions
                                .checked_add(self.proofs[*c].cost.functions)
                                .ok_or("proof cost overflow")?,
                            rules: sum
                                .rules
                                .checked_add(self.proofs[*c].cost.rules)
                                .ok_or("proof cost overflow")?,
                        })
                    },
                )?;
                (valid, cost)
            }
        };
        if !valid || cost != p.cost {
            return Err(format!(
                "invalid proof node: {}",
                self.proofs.expression(id, self.types)
            ));
        }
        self.visiting.remove(&id);
        self.visited.insert(id);
        Ok(())
    }
}

/// Translation state for one external witness and all its reachable premises.
struct ProofImporter<'a> {
    /// Source type graph owning every endpoint and substitution identifier.
    source_types: &'a TypeStore,
    /// Source proof graph owning the input witness and its children.
    source_proofs: &'a ProofStore,
    /// Independently elaborated target graph used by the verifier.
    target_types: &'a mut TypeStore,
    /// Translated proof records, inserted after their children.
    target_proofs: &'a mut ProofStore,
    /// Translation of source type identifiers, computed at most once per node.
    types: HashMap<TypeId, TypeId>,
    /// Translation of source proof identifiers, preserving DAG sharing.
    proofs: HashMap<ProofId, ProofId>,
    /// Nodes currently being translated, used to detect cycles.
    visiting: HashSet<ProofId>,
}
impl ProofImporter<'_> {
    /// Translate children before inserting their parent, memoizing both type
    /// and proof identifiers. Reject missing source nodes and back edges.
    fn visit(&mut self, id: ProofId) -> Result<ProofId, String> {
        if let Some(&local) = self.proofs.get(&id) {
            return Ok(local);
        }
        if !self.visiting.insert(id) {
            return Err("proof contains a cycle".into());
        }
        let p = self
            .source_proofs
            .get(id)
            .ok_or("proof contains an invalid proof identifier")?;
        let input = self
            .target_types
            .import(self.source_types, p.input, &mut self.types)?;
        let output = self
            .target_types
            .import(self.source_types, p.output, &mut self.types)?;
        let node = match &p.node {
            ProofNode::Primitive {
                id,
                name,
                line,
                description,
                substitutions,
            } => ProofNode::Primitive {
                id: *id,
                name: name.clone(),
                line: *line,
                description: description.clone(),
                substitutions: substitutions
                    .iter()
                    .map(|(n, t)| {
                        Ok((
                            n.clone(),
                            self.target_types
                                .import(self.source_types, *t, &mut self.types)?,
                        ))
                    })
                    .collect::<Result<_, String>>()?,
            },
            ProofNode::Inference { rule, children } => ProofNode::Inference {
                rule: *rule,
                children: children
                    .iter()
                    .map(|c| self.visit(*c))
                    .collect::<Result<_, _>>()?,
            },
        };
        let local = self.target_proofs.insert(Proof {
            input,
            output,
            cost: p.cost,
            node,
        });
        self.visiting.remove(&id);
        self.proofs.insert(id, local);
        Ok(local)
    }
}
