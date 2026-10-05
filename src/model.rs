use crate::{ValidationError, syntax};
use std::{
    cmp::Ordering,
    collections::{BTreeMap, BTreeSet, HashMap},
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
    /// Canonical nodes; child identifiers index this vector.
    nodes: Vec<Type>,
    /// Lookup of existing nodes; keys contain identifiers, never recursive trees.
    interned: HashMap<Type, TypeId>,
    /// Source declarations indexed by their unique nominal names.
    declarations: BTreeMap<String, TypeInfo>,
    /// Resolved bodies of nominal specializations, including predefined `Bytes`.
    shapes: HashMap<TypeId, TypeId>,
}

impl TypeStore {
    /// Number of interned nodes, including bound variables and synthesized types.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Whether the store contains no nodes.
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Look up a node using an identifier originating from this store.
    pub fn get(&self, id: TypeId) -> Option<&Type> {
        self.nodes.get(id.0)
    }

    /// Find an already interned, normalized node using children from this store.
    pub fn find(&self, node: &Type) -> Option<TypeId> {
        self.interned.get(node).copied()
    }

    /// Format a semantic type with access to its child nodes.
    pub fn display(&self, id: TypeId) -> TypeDisplay<'_> {
        TypeDisplay { store: self, id }
    }

    /// Intern one node; only its immediate children are copied into the lookup key.
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
        if let Some(&id) = self.interned.get(&node) {
            return id;
        }
        let id = TypeId(self.nodes.len());
        self.nodes.push(node.clone());
        self.interned.insert(node, id);
        id
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

    pub(crate) fn source_variants(&self, id: TypeId) -> BTreeSet<TypeId> {
        self.outer_variants(id).into_iter().collect()
    }

    pub(crate) fn handled_variants(&self, id: TypeId) -> BTreeSet<TypeId> {
        match &self[id] {
            Type::Sum(items) => items.iter().copied().collect(),
            _ => [id].into_iter().collect(),
        }
    }

    pub(crate) fn union(&mut self, items: Vec<TypeId>) -> TypeId {
        self.intern(Type::Sum(items))
    }

    pub(crate) fn depth(&self, id: TypeId) -> usize {
        match &self[id] {
            Type::Unit | Type::Named(..) | Type::Var(..) | Type::Exists(..) => 0,
            Type::Sum(items) => items.iter().map(|t| self.depth(*t)).max().unwrap_or(0),
            Type::List(item) | Type::Set(item) => 1 + self.depth(*item),
            Type::Map(a, b) => 1 + self.depth(*a).max(self.depth(*b)),
            Type::Product(items) => 1 + items.iter().map(|t| self.depth(*t)).max().unwrap_or(0),
        }
    }

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
    pub(crate) fn collect(&mut self, id: TypeId, out: &mut BTreeSet<TypeId>) {
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

    pub(crate) fn parameter_environments(
        &mut self,
        parameters: &[syntax::Binder],
        line: usize,
    ) -> Result<Vec<BTreeMap<String, TypeId>>, ValidationError> {
        self.parameter_environments_with_parent(parameters, &BTreeMap::new(), line)
    }

    fn parameter_environments_with_parent(
        &mut self,
        parameters: &[syntax::Binder],
        parent: &BTreeMap<String, TypeId>,
        line: usize,
    ) -> Result<Vec<BTreeMap<String, TypeId>>, ValidationError> {
        let mut envs = vec![parent.clone()];
        let mut names = BTreeSet::new();
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

    /// Collect declared ground families and their shapes, stopping at the type limit.
    /// The snapshot keeps declaration borrows separate from mutable graph construction.
    pub(crate) fn collect_declarations(
        &mut self,
        out: &mut BTreeSet<TypeId>,
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

    /// Transfer a type from a different store, translating every child identifier.
    /// Nominal applications are checked against this store's source declarations.
    pub(crate) fn import(
        &mut self,
        source: &Self,
        id: TypeId,
        memo: &mut HashMap<TypeId, TypeId>,
    ) -> Result<TypeId, String> {
        if let Some(&local) = memo.get(&id) {
            return Ok(local);
        }
        let source_node = source
            .get(id)
            .ok_or("proof contains an invalid type identifier")?;
        let node = match source_node {
            Type::Unit => Type::Unit,
            Type::Named(name, args) => {
                let args = args
                    .iter()
                    .map(|t| self.import(source, *t, memo))
                    .collect::<Result<_, _>>()?;
                let local = self.nominal(name, args, 0).map_err(|e| e.to_string())?;
                memo.insert(id, local);
                return Ok(local);
            }
            Type::List(t) => Type::List(self.import(source, *t, memo)?),
            Type::Set(t) => Type::Set(self.import(source, *t, memo)?),
            Type::Map(k, v) => Type::Map(
                self.import(source, *k, memo)?,
                self.import(source, *v, memo)?,
            ),
            Type::Product(items) => Type::Product(
                items
                    .iter()
                    .map(|t| self.import(source, *t, memo))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Sum(items) => Type::Sum(
                items
                    .iter()
                    .map(|t| self.import(source, *t, memo))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Exists(n, d, b) => Type::Exists(
                n.clone(),
                self.import(source, *d, memo)?,
                self.import(source, *b, memo)?,
            ),
            Type::Var(n, witnesses) => Type::Var(
                n.clone(),
                witnesses
                    .iter()
                    .map(|t| self.import(source, *t, memo))
                    .collect::<Result<_, _>>()?,
            ),
        };
        let local = self.intern(node);
        memo.insert(id, local);
        Ok(local)
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
    /// Concrete choices for declaration and enclosing trait parameters.
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
        for env in types.parameter_environments(&function.parameters, function.line)? {
            primitives.push(Primitive {
                name: function.name.clone(),
                input: types.resolve(&function.input, &env, function.line)?,
                output: types.resolve(&function.output, &env, function.line)?,
                line: function.line,
                description: function.description.clone(),
                substitutions: env,
            });
        }
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
    let mut names = BTreeSet::new();
    let mut features = Vec::new();
    for feature in &document.features {
        if !names.insert(&feature.name) {
            return Err(invalid(
                feature.line,
                format!("duplicate feature '{}'", feature.name),
            ));
        }
        for env in types.parameter_environments(&feature.parameters, feature.line)? {
            features.push(Primitive {
                name: feature.name.clone(),
                input: types.resolve(&feature.input, &env, feature.line)?,
                output: types.resolve(&feature.output, &env, feature.line)?,
                line: feature.line,
                description: feature.description.clone(),
                substitutions: env,
            });
        }
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

fn check_definition_cycles(document: &syntax::Document) -> Result<(), ValidationError> {
    let names = document
        .types
        .iter()
        .map(|item| item.name.as_str())
        .chain(document.traits.iter().map(|item| item.name.as_str()))
        .collect::<BTreeSet<_>>();
    let mut graph = BTreeMap::<String, BTreeSet<String>>::new();
    for declaration in &document.traits {
        let mut references = BTreeSet::new();
        for binder in &declaration.parameters {
            collect_references(&binder.domain, &names, &mut references);
        }
        graph.insert(declaration.name.clone(), references);
    }
    for declaration in &document.types {
        let mut references = BTreeSet::new();
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

    fn visit(
        name: &str,
        graph: &BTreeMap<String, BTreeSet<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
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

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
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

fn collect_references(
    expr: &syntax::TypeExpr,
    declared: &BTreeSet<&str>,
    out: &mut BTreeSet<String>,
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

fn builtin_names() -> BTreeSet<&'static str> {
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

fn check_overloads(primitives: &[Primitive], types: &mut TypeStore) -> Result<(), ValidationError> {
    let mut by_name = BTreeMap::<&str, Vec<&Primitive>>::new();
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
