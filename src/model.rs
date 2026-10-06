use crate::{ValidationError, syntax};
use indexmap::{IndexMap, IndexSet};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, HashMap, HashSet},
    fmt,
    ops::Index,
};

/// Index of an immutable type node in its owning `TypeStore`.
/// Identifiers can be copied cheaply, but are meaningful only within that store.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct TypeId(usize);

/// A semantic type node whose children are identifiers in the same store.
/// Nominal identity is preserved; anonymous sums are normalized when interned.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Type {
    /// The empty product `()`, distinct from the built-in absence marker `None`.
    Unit,
    /// A nominal type or ground family application, with ordered arguments.
    Named(String, Vec<TypeId>),
    /// An anonymous finite sequence; order and repetitions are significant.
    List(TypeId),
    /// An anonymous finite set of element values.
    Set(TypeId),
    /// An anonymous finite partial mapping from keys to values.
    Map(TypeId, TypeId),
    /// An ordered product; components are never implicitly flattened.
    Product(Vec<TypeId>),
    /// Flattened, sorted, deduplicated anonymous alternatives.
    Sum(Vec<TypeId>),
    /// An existential package: canonical binder name, finite domain, and body.
    Exists(String, TypeId, TypeId),
    /// A bound existential variable and its allowed witnesses.
    Var(String, Vec<TypeId>),
}

/// Owner of the semantic type graph and the nominal declaration registry.
/// Nodes are append-only. Interning reuses an identifier for equal nodes, and
/// resolved nominal bodies are cached as directed structural views.
#[derive(Clone, Debug, Default)]
pub struct TypeStore {
    /// Canonical nodes stored once, with hash lookup and stable insertion indices.
    nodes: IndexSet<Type>,
    /// Source declarations indexed by name, retaining their registration order.
    declarations: IndexMap<String, TypeInfo>,
    /// Resolved bodies of nominal specializations, including predefined `Bytes`.
    shapes: HashMap<TypeId, TypeId>,
}

impl TypeStore {
    /// Look up a node using an identifier originating from this store.
    pub fn get(&self, id: TypeId) -> Option<&Type> {
        self.nodes.get_index(id.0)
    }

    /// Find an already interned, normalized node using children from this store.
    pub fn find(&self, node: &Type) -> Option<TypeId> {
        self.nodes.get_index_of(node).map(TypeId)
    }

    /// Format a semantic type with access to its child nodes.
    pub fn display(&self, id: TypeId) -> TypeDisplay<'_> {
        TypeDisplay { store: self, id }
    }

    /// Normalize and intern one node, reusing its existing insertion index.
    /// Empty products become unit; anonymous sums are flattened, sorted by
    /// semantic structure, and deduplicated. Nominal nodes retain their identity.
    pub(crate) fn intern(&mut self, node: Type) -> TypeId {
        let node = match node {
            Type::Product(items) if items.is_empty() => Type::Unit,
            Type::Sum(items) => {
                let mut flat = Vec::new();
                for item in items {
                    match &self[item] {
                        Type::Sum(inner) => flat.extend_from_slice(inner),
                        _ => flat.push(item),
                    }
                }
                flat.sort_unstable_by(|a, b| self.compare(*a, *b));
                flat.dedup();
                if flat.len() == 1 {
                    return flat[0];
                }
                Type::Sum(flat)
            }
            other => other,
        };
        TypeId(self.nodes.insert_full(node).0)
    }

    /// Compare structure for deterministic presentation, independently of allocation order.
    pub(crate) fn compare(&self, left: TypeId, right: TypeId) -> Ordering {
        if left == right {
            return Ordering::Equal;
        }
        fn rank(node: &Type) -> u8 {
            match node {
                Type::Unit => 0,
                Type::Named(..) => 1,
                Type::List(..) => 2,
                Type::Set(..) => 3,
                Type::Map(..) => 4,
                Type::Product(..) => 5,
                Type::Sum(..) => 6,
                Type::Exists(..) => 7,
                Type::Var(..) => 8,
            }
        }
        let a = &self[left];
        let b = &self[right];
        rank(a).cmp(&rank(b)).then_with(|| match (a, b) {
            (Type::Unit, Type::Unit) => Ordering::Equal,
            (Type::Named(n, a), Type::Named(m, b)) | (Type::Var(n, a), Type::Var(m, b)) => {
                n.cmp(m).then_with(|| self.compare_lists(a, b))
            }
            (Type::List(a), Type::List(b)) | (Type::Set(a), Type::Set(b)) => self.compare(*a, *b),
            (Type::Map(a, b), Type::Map(c, d)) => {
                self.compare(*a, *c).then_with(|| self.compare(*b, *d))
            }
            (Type::Product(a), Type::Product(b)) | (Type::Sum(a), Type::Sum(b)) => {
                self.compare_lists(a, b)
            }
            (Type::Exists(n, a, b), Type::Exists(m, c, d)) => n
                .cmp(m)
                .then_with(|| self.compare(*a, *c))
                .then_with(|| self.compare(*b, *d)),
            _ => unreachable!("different variants have different ranks"),
        })
    }

    fn compare_lists(&self, left: &[TypeId], right: &[TypeId]) -> Ordering {
        left.iter()
            .zip(right)
            .map(|(a, b)| self.compare(*a, *b))
            .find(|order| *order != Ordering::Equal)
            .unwrap_or_else(|| left.len().cmp(&right.len()))
    }

    /// Expose one declared structural description without constructing its reverse.
    pub(crate) fn shape(&self, id: TypeId) -> TypeId {
        self.shapes.get(&id).copied().unwrap_or(id)
    }

    /// Immediate variants of an anonymous or directly declared nominal sum.
    pub(crate) fn outer_variants(&self, id: TypeId) -> Vec<TypeId> {
        match &self[self.shape(id)] {
            Type::Sum(items) => items.clone(),
            _ => vec![id],
        }
    }

    /// Alternatives available in a supplied value, exposing the direct body of
    /// a nominal sum. Non-sum types contribute their original nominal identity.
    pub(crate) fn source_variants(&self, id: TypeId) -> IndexSet<TypeId> {
        self.outer_variants(id).into_iter().collect()
    }

    /// Alternatives explicitly accepted by a morphism's input signature.
    /// Only anonymous sums are expanded; a nominal input stays a single type.
    pub(crate) fn handled_variants(&self, id: TypeId) -> IndexSet<TypeId> {
        match &self[id] {
            Type::Sum(items) => items.iter().copied().collect(),
            _ => [id].into_iter().collect(),
        }
    }

    /// Construct a normalized anonymous union, flattening nested sums while
    /// preserving nominal alternatives and reusing any already interned result.
    pub(crate) fn union(&mut self, items: Vec<TypeId>) -> TypeId {
        self.intern(Type::Sum(items))
    }

    /// Measure synthesized collection/product nesting for the search bound.
    /// Sums take their maximum alternative depth; named types and existential
    /// packages count as atoms, without expanding their structural descriptions.
    pub(crate) fn depth(&self, id: TypeId) -> usize {
        match &self[id] {
            Type::Unit | Type::Named(..) | Type::Var(..) | Type::Exists(..) => 0,
            Type::Sum(items) => items.iter().map(|t| self.depth(*t)).max().unwrap_or(0),
            Type::List(item) | Type::Set(item) => 1 + self.depth(*item),
            Type::Map(a, b) => 1 + self.depth(*a).max(self.depth(*b)),
            Type::Product(items) => 1 + items.iter().map(|t| self.depth(*t)).max().unwrap_or(0),
        }
    }

    /// Decide whether an input contract accepts a supplied type through anonymous
    /// sum inclusion or componentwise product matching. Nominal structural views
    /// and collection covariance are not implicit parts of input compatibility.
    pub(crate) fn accepts(&self, contract: TypeId, supplied: TypeId) -> bool {
        if contract == supplied {
            return true;
        }
        match (&self[contract], &self[supplied]) {
            (Type::Sum(_), Type::Sum(items)) => items.iter().all(|i| self.accepts(contract, *i)),
            (Type::Sum(items), _) => items.iter().any(|i| self.accepts(*i, supplied)),
            (Type::Product(a), Type::Product(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|(a, b)| self.accepts(*a, *b))
            }
            _ => false,
        }
    }

    /// Collect ground subexpressions, specializing existential bodies only for enumeration.
    /// The output set also marks visited nodes. Existential witnesses add concrete
    /// body types to the universe, without granting package construction or unpacking.
    pub(crate) fn collect(&mut self, id: TypeId, out: &mut IndexSet<TypeId>) {
        if !out.insert(id) {
            return;
        }
        match self[id].clone() {
            Type::Named(_, args) | Type::Product(args) | Type::Sum(args) => {
                for arg in args {
                    self.collect(arg, out);
                }
            }
            Type::List(item) | Type::Set(item) => self.collect(item, out),
            Type::Map(k, v) => {
                self.collect(k, out);
                self.collect(v, out);
            }
            Type::Exists(name, domain, body) => {
                self.collect(domain, out);
                if let Some(variable) = self.find_variable(body, &name) {
                    let Type::Var(_, witnesses) = self[variable].clone() else {
                        unreachable!()
                    };
                    for witness in witnesses {
                        let ground = self.substitute(body, &name, witness);
                        self.collect(ground, out);
                    }
                } else {
                    self.collect(body, out);
                }
            }
            Type::Unit | Type::Var(..) => {}
        }
    }

    /// Find the first occurrence of a canonical bound variable in a type body,
    /// so enumeration can obtain its finite witnesses without unpacking a value.
    fn find_variable(&self, id: TypeId, name: &str) -> Option<TypeId> {
        match &self[id] {
            Type::Var(n, _) if n == name => Some(id),
            Type::Named(_, a) | Type::Product(a) | Type::Sum(a) => {
                a.iter().find_map(|t| self.find_variable(*t, name))
            }
            Type::List(a) | Type::Set(a) => self.find_variable(*a, name),
            Type::Map(a, b) => self
                .find_variable(*a, name)
                .or_else(|| self.find_variable(*b, name)),
            Type::Exists(_, _, body) => self.find_variable(*body, name),
            _ => None,
        }
    }

    /// Specialize a type body for one finite existential witness. Rebuild affected
    /// constructors through interning, normalize resulting sums, and resolve the
    /// structural views of newly concrete nominal applications.
    fn substitute(&mut self, id: TypeId, name: &str, value: TypeId) -> TypeId {
        let node = match self[id].clone() {
            Type::Var(n, _) if n == name => return value,
            Type::Named(n, a) => {
                let args = a
                    .into_iter()
                    .map(|t| self.substitute(t, name, value))
                    .collect();
                return self
                    .nominal(&n, args, 0)
                    .expect("specialization preserves declared domains");
            }
            Type::Product(a) => Type::Product(
                a.into_iter()
                    .map(|t| self.substitute(t, name, value))
                    .collect(),
            ),
            Type::Sum(a) => Type::Sum(
                a.into_iter()
                    .map(|t| self.substitute(t, name, value))
                    .collect(),
            ),
            Type::List(a) => Type::List(self.substitute(a, name, value)),
            Type::Set(a) => Type::Set(self.substitute(a, name, value)),
            Type::Map(a, b) => Type::Map(
                self.substitute(a, name, value),
                self.substitute(b, name, value),
            ),
            Type::Exists(n, d, b) => Type::Exists(n, d, self.substitute(b, name, value)),
            _ => return id,
        };
        self.intern(node)
    }

    /// Find the largest explicit product width anywhere in an expression,
    /// including generic arguments and existential domains and bodies. Elaboration
    /// uses this to infer the tuple-width bound after adding trait receivers.
    fn max_tuple_arity(&self, id: TypeId) -> usize {
        match &self[id] {
            Type::Product(items) => items.len().max(
                items
                    .iter()
                    .map(|t| self.max_tuple_arity(*t))
                    .max()
                    .unwrap_or(0),
            ),
            Type::Named(_, items) | Type::Sum(items) | Type::Var(_, items) => items
                .iter()
                .map(|t| self.max_tuple_arity(*t))
                .max()
                .unwrap_or(0),
            Type::List(item) | Type::Set(item) => self.max_tuple_arity(*item),
            Type::Map(a, b) | Type::Exists(_, a, b) => {
                self.max_tuple_arity(*a).max(self.max_tuple_arity(*b))
            }
            Type::Unit => 0,
        }
    }

    /// Validate a nominal application and cache its direct structural view.
    /// Check parameter arity and finite domains before resolving the declared body.
    /// A cached specialization needs no repeated elaboration; opaque declarations
    /// view themselves, and predefined `Bytes` exposes `List<Byte>`.
    fn nominal(
        &mut self,
        name: &str,
        args: Vec<TypeId>,
        line: usize,
    ) -> Result<TypeId, ValidationError> {
        let node = Type::Named(name.to_owned(), args.clone());
        if let Some(id) = self.find(&node) {
            if self.shapes.contains_key(&id) {
                return Ok(id);
            }
        }
        let info = self.declarations.get(name).cloned();
        if let Some(info) = &info {
            if info.parameters.len() != args.len() {
                return Err(invalid(
                    line,
                    format!(
                        "type '{name}' expects {} argument(s), got {}",
                        info.parameters.len(),
                        args.len()
                    ),
                ));
            }
            for (binder, arg) in info.parameters.iter().zip(&args) {
                let domain = self.resolve(&binder.domain, &BTreeMap::new(), line)?;
                let permitted = self.outer_variants(domain);
                let valid = match &self[*arg] {
                    Type::Var(_, witnesses) => witnesses.iter().all(|w| permitted.contains(w)),
                    _ => permitted.contains(arg),
                };
                if !valid {
                    return Err(invalid(
                        line,
                        format!(
                            "type argument {} is outside the domain of {name}<{}>",
                            self.display(*arg),
                            binder.name
                        ),
                    ));
                }
            }
        } else if !builtin_names().contains(name) || matches!(name, "List" | "Set" | "Map") {
            return Err(invalid(line, format!("unknown type '{name}'")));
        } else if !args.is_empty() {
            return Err(invalid(
                line,
                format!("built-in type {name} does not take arguments"),
            ));
        }
        let id = self.intern(node);
        let shape = if name == "Bytes" {
            let byte = self.intern(Type::Named("Byte".to_owned(), Vec::new()));
            self.intern(Type::List(byte))
        } else if let Some(TypeInfo {
            parameters,
            body: Some(body),
        }) = info
        {
            let env = parameters
                .iter()
                .zip(args)
                .map(|(b, a)| (b.name.clone(), a))
                .collect();
            self.resolve(&body, &env, line)?
        } else {
            id
        };
        self.shapes.insert(id, shape);
        Ok(id)
    }

    /// Resolve syntax into this store using the supplied parameter substitutions.
    /// Validate names, constructor arities, finite domains, and binder scopes;
    /// normalize algebraic expressions and canonicalize existential binder names
    /// so alpha-equivalent packages receive the same identifier.
    pub(crate) fn resolve(
        &mut self,
        expr: &syntax::TypeExpr,
        env: &BTreeMap<String, TypeId>,
        line: usize,
    ) -> Result<TypeId, ValidationError> {
        let node = match expr {
            syntax::TypeExpr::Name(name, args) => {
                if let Some(&value) = env.get(name) {
                    if !args.is_empty() {
                        return Err(invalid(
                            line,
                            format!("type parameter '{name}' cannot have arguments"),
                        ));
                    }
                    return Ok(value);
                }
                let args = args
                    .iter()
                    .map(|arg| self.resolve(arg, env, line))
                    .collect::<Result<Vec<_>, _>>()?;
                match (name.as_str(), args.as_slice()) {
                    ("List", [item]) => Type::List(*item),
                    ("Set", [item]) => Type::Set(*item),
                    ("Map", [key, value]) => Type::Map(*key, *value),
                    ("List" | "Set" | "Map", _) => {
                        return Err(invalid(line, format!("wrong arity for {name}")));
                    }
                    _ => return self.nominal(name, args, line),
                }
            }
            syntax::TypeExpr::Sum(items) => Type::Sum(
                items
                    .iter()
                    .map(|item| self.resolve(item, env, line))
                    .collect::<Result<_, _>>()?,
            ),
            syntax::TypeExpr::Product(items) => Type::Product(
                items
                    .iter()
                    .map(|item| self.resolve(item, env, line))
                    .collect::<Result<_, _>>()?,
            ),
            syntax::TypeExpr::Exists(binder, body) => {
                let domain = self.resolve(&binder.domain, &BTreeMap::new(), line)?;
                let variants = self.outer_variants(domain);
                if variants.is_empty() {
                    return Err(invalid(line, "existential domain is empty"));
                }
                if env.contains_key(&binder.name) {
                    return Err(invalid(
                        line,
                        "existential binder shadows an outer parameter",
                    ));
                }
                let canonical = format!(
                    "T{}",
                    env.values()
                        .filter(|t| matches!(self[**t], Type::Var(..)))
                        .count()
                );
                let variable = self.intern(Type::Var(canonical.clone(), variants));
                let mut nested = env.clone();
                nested.insert(binder.name.clone(), variable);
                let body = self.resolve(body, &nested, line)?;
                Type::Exists(canonical, domain, body)
            }
        };
        Ok(self.intern(node))
    }

    /// Expand closed finite parameter domains into every concrete substitution.
    /// Multiple parameters form a Cartesian product; an empty parameter list
    /// yields one empty environment so non-generic declarations expand once.
    /// Environments keep name order because they also become canonical proof
    /// substitutions, whose ordered entries are hashed and displayed.
    pub(crate) fn parameter_environments(
        &mut self,
        parameters: &[syntax::Binder],
        line: usize,
    ) -> Result<Vec<BTreeMap<String, TypeId>>, ValidationError> {
        self.parameter_environments_with_parent(parameters, &BTreeMap::new(), line)
    }

    /// Extend an enclosing trait environment with member parameters. Domains
    /// resolve in an empty environment, so they cannot depend on earlier choices.
    /// Reject duplicate or shadowing names and stop at the specialization guard.
    fn parameter_environments_with_parent(
        &mut self,
        parameters: &[syntax::Binder],
        parent: &BTreeMap<String, TypeId>,
        line: usize,
    ) -> Result<Vec<BTreeMap<String, TypeId>>, ValidationError> {
        let mut envs = vec![parent.clone()];
        let mut names = HashSet::new();
        for binder in parameters {
            if !names.insert(binder.name.clone()) || parent.contains_key(&binder.name) {
                return Err(invalid(
                    line,
                    format!(
                        "type parameter '{}' is duplicated or shadows an outer parameter",
                        binder.name
                    ),
                ));
            }
            let domain = self.resolve(&binder.domain, &BTreeMap::new(), line)?;
            let variants = self.outer_variants(domain);
            if variants.is_empty() {
                return Err(invalid(
                    line,
                    format!("type parameter '{}' has an empty domain", binder.name),
                ));
            }
            let mut next = Vec::new();
            for env in &envs {
                for &variant in &variants {
                    let mut extended = env.clone();
                    extended.insert(binder.name.clone(), variant);
                    if next.len() >= 100_000 {
                        return Err(ValidationError::ExpansionLimit {
                            line,
                            limit: 100_000,
                        });
                    }
                    next.push(extended);
                }
            }
            envs = next;
        }
        Ok(envs)
    }

    /// Expand a function or feature into ground signatures using its finite parameters.
    /// This only resolves signatures; the caller decides whether they are available
    /// morphisms or verification goals and applies the corresponding name checks.
    fn expand_function(
        &mut self,
        function: &syntax::FunctionDecl,
    ) -> Result<Vec<Primitive>, ValidationError> {
        self.parameter_environments(&function.parameters, function.line)?
            .into_iter()
            .map(|env| {
                Ok(Primitive {
                    name: function.name.clone(),
                    input: self.resolve(&function.input, &env, function.line)?,
                    output: self.resolve(&function.output, &env, function.line)?,
                    line: function.line,
                    description: function.description.clone(),
                    substitutions: env,
                })
            })
            .collect()
    }

    /// Collect declared ground families and their shapes, stopping at the type limit.
    /// The snapshot keeps declaration borrows separate from mutable graph construction.
    pub(crate) fn collect_declarations(
        &mut self,
        out: &mut IndexSet<TypeId>,
        limit: usize,
    ) -> Result<(), String> {
        let declarations = self
            .declarations
            .iter()
            .map(|(n, d)| (n.clone(), d.parameters.clone()))
            .collect::<Vec<_>>();
        for (name, parameters) in declarations {
            for env in self
                .parameter_environments(&parameters, 0)
                .map_err(|error| error.to_string())?
            {
                let args = parameters.iter().map(|b| env[&b.name]).collect();
                let named = self
                    .nominal(&name, args, 0)
                    .map_err(|error| error.to_string())?;
                self.collect(named, out);
                self.collect(self.shape(named), out);
                if out.len() > limit {
                    return Err("ground declarations exceed --max-types".into());
                }
            }
        }
        Ok(())
    }
}

impl Index<TypeId> for TypeStore {
    type Output = Type;
    fn index(&self, id: TypeId) -> &Type {
        &self.nodes[id.0]
    }
}

/// A borrowed type together with the store needed to format its children.
pub struct TypeDisplay<'a> {
    /// Store owning the displayed type and all its descendants.
    store: &'a TypeStore,
    /// Root node to display.
    id: TypeId,
}
impl fmt::Display for TypeDisplay<'_> {
    /// Follow child identifiers to render semantic types, preserving nominal
    /// names, product nesting, and the scope of existential sum alternatives.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let store = self.store;
        match &store[self.id] {
            Type::Unit => f.write_str("()"),
            Type::Named(name, args) if args.is_empty() => f.write_str(name),
            Type::Named(name, args) => {
                write!(f, "{name}<")?;
                fmt_type_list(store, args, f)?;
                f.write_str(">")
            }
            Type::List(item) => write!(f, "List<{}>", store.display(*item)),
            Type::Set(item) => write!(f, "Set<{}>", store.display(*item)),
            Type::Map(key, value) => {
                write!(f, "Map<{}, {}>", store.display(*key), store.display(*value))
            }
            Type::Product(items) => {
                f.write_str("(")?;
                fmt_type_list(store, items, f)?;
                f.write_str(")")
            }
            Type::Sum(items) => {
                for (index, &item) in items.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" | ")?;
                    }
                    if matches!(store[item], Type::Exists(..)) {
                        write!(f, "({})", store.display(item))?;
                    } else {
                        write!(f, "{}", store.display(item))?;
                    }
                }
                Ok(())
            }
            Type::Exists(name, domain, body) => write!(
                f,
                "exists {name} from {}: {}",
                store.display(*domain),
                store.display(*body)
            ),
            Type::Var(name, _) => f.write_str(name),
        }
    }
}

/// Format a comma-separated list of types without enclosing delimiters.
fn fmt_type_list(store: &TypeStore, items: &[TypeId], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for (index, &item) in items.iter().enumerate() {
        if index > 0 {
            f.write_str(", ")?;
        }
        write!(f, "{}", store.display(item))?;
    }
    Ok(())
}

/// Source declaration of a nominal type or trait, before finite specialization.
#[derive(Clone, Debug)]
pub(crate) struct TypeInfo {
    /// Finite parameters of the nominal family, in declaration order.
    parameters: Vec<syntax::Binder>,
    /// Structural description granting a directed view, if one was declared.
    body: Option<syntax::TypeExpr>,
}

/// One ground callable signature, retaining its source contract and substitutions.
#[derive(Clone, Debug)]
pub(crate) struct Primitive {
    /// Original qualified function or feature name.
    pub(crate) name: String,
    /// Resolved input, including the receiver introduced by trait lowering.
    pub(crate) input: TypeId,
    /// Resolved output preserving every declared alternative.
    pub(crate) output: TypeId,
    /// One-based declaration line for diagnostics and proof references.
    pub(crate) line: usize,
    /// Semantic prose attached to the source declaration.
    pub(crate) description: String,
    /// Concrete choices in name order for canonical proof hashing and display.
    pub(crate) substitutions: BTreeMap<String, TypeId>,
}

/// Checked declarations and their shared type store, ready for proof search.
pub(crate) struct Specification {
    /// Tuple-width bound inferred from explicit shapes after trait lowering.
    pub(crate) tuple_arity: usize,
    /// Owner of resolved type nodes, declaration names, and structural views.
    pub(crate) types: TypeStore,
    /// Ground morphisms provided exclusively by `DEFINITIONS`.
    pub(crate) primitives: Vec<Primitive>,
    /// Ground feature goals, kept separate from available morphisms.
    pub(crate) features: Vec<Primitive>,
}

/// Register declarations and transform the parsed document into ground signatures.
/// Reject definition cycles before resolving bodies, validate even unused types,
/// expand finite parameters, and lower trait members by adding their receivers.
/// Finally check overload intersections and infer the explicit tuple-width bound.
/// Feature signatures remain separate goals and never become available morphisms.
pub(crate) fn elaborate(document: &syntax::Document) -> Result<Specification, ValidationError> {
    let builtins = builtin_names();
    let mut types = TypeStore::default();
    for declaration in &document.types {
        if builtins.contains(declaration.name.as_str()) {
            return Err(invalid(
                declaration.line,
                format!("built-in type '{}' cannot be redeclared", declaration.name),
            ));
        }
        if types.declarations.contains_key(&declaration.name) {
            return Err(invalid(
                declaration.line,
                format!("duplicate type declaration '{}'", declaration.name),
            ));
        }
        types
            .declarations
            .insert(declaration.name.clone(), TypeInfo {
                parameters: declaration.parameters.clone(),
                body: declaration.body.clone(),
            });
    }
    for declaration in &document.traits {
        if builtins.contains(declaration.name.as_str())
            || types.declarations.contains_key(&declaration.name)
        {
            return Err(invalid(
                declaration.line,
                format!("duplicate or reserved type '{}'", declaration.name),
            ));
        }
        types
            .declarations
            .insert(declaration.name.clone(), TypeInfo {
                parameters: declaration.parameters.clone(),
                body: None,
            });
    }
    check_definition_cycles(document)?;
    let mut tuple_arity = 2;
    for declaration in &document.types {
        for env in types.parameter_environments(&declaration.parameters, declaration.line)? {
            for &value in env.values() {
                tuple_arity = tuple_arity.max(types.max_tuple_arity(value));
            }
            if let Some(body) = &declaration.body {
                let body = types.resolve(body, &env, declaration.line)?;
                tuple_arity = tuple_arity.max(types.max_tuple_arity(body));
            }
        }
    }
    for declaration in &document.traits {
        types.parameter_environments(&declaration.parameters, declaration.line)?;
    }
    let mut primitives = Vec::new();
    for function in &document.functions {
        primitives.extend(types.expand_function(function)?);
    }
    for declaration in &document.traits {
        for trait_env in types.parameter_environments(&declaration.parameters, declaration.line)? {
            let args = declaration
                .parameters
                .iter()
                .map(|b| trait_env[&b.name])
                .collect();
            let receiver = types.nominal(&declaration.name, args, declaration.line)?;
            for member in &declaration.members {
                for env in types.parameter_environments_with_parent(
                    &member.parameters,
                    &trait_env,
                    member.line,
                )? {
                    let member_input = types.resolve(&member.input, &env, member.line)?;
                    let output = types.resolve(&member.output, &env, member.line)?;
                    let input = match &types[member_input] {
                        Type::Unit => receiver,
                        Type::Product(items) => {
                            let mut tuple = vec![receiver];
                            tuple.extend_from_slice(items);
                            types.intern(Type::Product(tuple))
                        }
                        _ => types.intern(Type::Product(vec![receiver, member_input])),
                    };
                    primitives.push(Primitive {
                        name: format!("{}.{}", declaration.name, member.name),
                        input,
                        output,
                        line: member.line,
                        description: member.description.clone(),
                        substitutions: env,
                    });
                }
            }
        }
    }
    let mut names = HashSet::new();
    let mut features = Vec::new();
    for feature in &document.features {
        if !names.insert(&feature.name) {
            return Err(invalid(
                feature.line,
                format!("duplicate feature '{}'", feature.name),
            ));
        }
        features.extend(types.expand_function(feature)?);
    }
    check_overloads(&primitives, &mut types)?;
    for function in primitives.iter().chain(&features) {
        tuple_arity = tuple_arity
            .max(types.max_tuple_arity(function.input))
            .max(types.max_tuple_arity(function.output));
    }
    Ok(Specification {
        tuple_arity,
        types,
        primitives,
        features,
    })
}

/// Reject dependency cycles through structural bodies and parameter domains before
/// recursive elaboration starts. Bound variables do not create declaration edges;
/// active DFS marks distinguish a cycle from an already completed dependency.
/// Visit declarations and references in insertion order for reproducible diagnostics.
fn check_definition_cycles(document: &syntax::Document) -> Result<(), ValidationError> {
    let names = document
        .types
        .iter()
        .map(|item| item.name.as_str())
        .chain(document.traits.iter().map(|item| item.name.as_str()))
        .collect::<HashSet<_>>();
    let mut graph = IndexMap::<String, IndexSet<String>>::new();
    for declaration in &document.traits {
        let mut references = IndexSet::new();
        for binder in &declaration.parameters {
            collect_references(&binder.domain, &names, &mut references);
        }
        graph.insert(declaration.name.clone(), references);
    }
    for declaration in &document.types {
        let mut references = IndexSet::new();
        for binder in &declaration.parameters {
            collect_references(&binder.domain, &names, &mut references);
        }
        if let Some(body) = &declaration.body {
            let unbound = names
                .iter()
                .copied()
                .filter(|name| !declaration.parameters.iter().any(|b| b.name == *name))
                .collect();
            collect_references(body, &unbound, &mut references);
        }
        graph.insert(declaration.name.clone(), references);
    }

    /// Return a declaration on a back edge, or mark its dependency subtree complete.
    fn visit(
        name: &str,
        graph: &IndexMap<String, IndexSet<String>>,
        visiting: &mut HashSet<String>,
        visited: &mut HashSet<String>,
    ) -> Option<String> {
        if visited.contains(name) {
            return None;
        }
        if !visiting.insert(name.to_owned()) {
            return Some(name.to_owned());
        }
        if let Some(edges) = graph.get(name) {
            for target in edges {
                if let Some(cycle) = visit(target, graph, visiting, visited) {
                    return Some(cycle);
                }
            }
        }
        visiting.remove(name);
        visited.insert(name.to_owned());
        None
    }

    let mut visiting = HashSet::new();
    let mut visited = HashSet::new();
    for name in graph.keys() {
        if let Some(cycle) = visit(name, &graph, &mut visiting, &mut visited) {
            let line = document
                .types
                .iter()
                .find(|item| item.name == cycle)
                .map_or(1, |item| item.line);
            return Err(invalid(
                line,
                format!("cyclic structural type definition involving '{cycle}'"),
            ));
        }
    }
    Ok(())
}

/// Collect referenced declaration names for cycle detection, descending into type
/// arguments and algebraic expressions while respecting existential binder scope.
fn collect_references(
    expr: &syntax::TypeExpr,
    declared: &HashSet<&str>,
    out: &mut IndexSet<String>,
) {
    match expr {
        syntax::TypeExpr::Name(name, args) => {
            if declared.contains(name.as_str()) {
                out.insert(name.clone());
            }
            for arg in args {
                collect_references(arg, declared, out);
            }
        }
        syntax::TypeExpr::Sum(items) | syntax::TypeExpr::Product(items) => {
            for item in items {
                collect_references(item, declared, out);
            }
        }
        syntax::TypeExpr::Exists(binder, body) => {
            collect_references(&binder.domain, declared, out);
            let unbound = declared
                .iter()
                .copied()
                .filter(|name| *name != binder.name)
                .collect();
            collect_references(body, &unbound, out);
        }
    }
}

fn builtin_names() -> HashSet<&'static str> {
    [
        "Boolean", "Int8", "Int16", "Int32", "Int64", "UInt8", "UInt16", "UInt32", "UInt64",
        "Byte", "Float32", "Float64", "None", "String", "Bytes", "List", "Set", "Map",
    ]
    .into_iter()
    .collect()
}

fn invalid(line: usize, message: impl Into<String>) -> ValidationError {
    ValidationError::Invalid(format!("line {line}: {}", message.into()))
}

/// Reject any two ground specializations of the same function name whose input
/// contracts overlap, including specializations produced from one generic source.
/// Report a common accepted input as a witness; no specificity tie-break is used.
/// Check name groups in first-occurrence order so error selection is reproducible.
fn check_overloads(primitives: &[Primitive], types: &mut TypeStore) -> Result<(), ValidationError> {
    let mut by_name = IndexMap::<&str, Vec<&Primitive>>::new();
    for primitive in primitives {
        by_name.entry(&primitive.name).or_default().push(primitive);
    }
    for (name, declarations) in by_name {
        for left in 0..declarations.len() {
            for right in left + 1..declarations.len() {
                let a = declarations[left];
                let b = declarations[right];
                if let Some(witness) = overlap_witness(a.input, b.input, types) {
                    return Err(invalid(
                        b.line,
                        format!(
                            "ambiguous overload '{name}': input {} (line {}) overlaps input {} (line {}); common input: {}",
                            types.display(a.input),
                            a.line,
                            types.display(b.input),
                            b.line,
                            types.display(witness)
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Construct one common input for two contracts by matching sum alternatives and
/// product components. Other types overlap only by identical nominal/structural
/// identifiers; declared views do not make separate nominal types interchangeable.
fn overlap_witness(left: TypeId, right: TypeId, types: &mut TypeStore) -> Option<TypeId> {
    match (types[left].clone(), types[right].clone()) {
        (Type::Sum(items), _) => items
            .into_iter()
            .find_map(|item| overlap_witness(item, right, types)),
        (_, Type::Sum(items)) => items
            .into_iter()
            .find_map(|item| overlap_witness(left, item, types)),
        (Type::Product(a), Type::Product(b)) if a.len() == b.len() => {
            let items = a
                .into_iter()
                .zip(b)
                .map(|(a, b)| overlap_witness(a, b, types))
                .collect::<Option<Vec<_>>>()?;
            Some(types.intern(Type::Product(items)))
        }
        _ if left == right => Some(left),
        _ => None,
    }
}

#[cfg(test)]
mod tests;
