use self::Type as Ty;
use crate::{ValidationError, syntax};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Type {
    Unit,
    Named(String, Vec<Ty>),
    List(Box<Ty>),
    Set(Box<Ty>),
    Map(Box<Ty>, Box<Ty>),
    Product(Vec<Ty>),
    Sum(Vec<Ty>),
    Exists(String, Box<Ty>, Box<Ty>),
    Var(String, Vec<Ty>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unit => f.write_str("()"),
            Self::Named(name, args) if args.is_empty() => f.write_str(name),
            Self::Named(name, args) => {
                write!(f, "{name}<")?;
                for (index, item) in args.iter().enumerate() {
                    if index > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_str(">")
            }
            Self::List(item) => write!(f, "List<{item}>"),
            Self::Set(item) => write!(f, "Set<{item}>"),
            Self::Map(key, value) => write!(f, "Map<{key}, {value}>"),
            Self::Product(items) => {
                f.write_str("(")?;
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_str(")")
            }
            Self::Sum(items) => {
                for (index, item) in items.iter().enumerate() {
                    if index > 0 {
                        f.write_str(" | ")?;
                    }
                    if matches!(item, Self::Exists(_, _, _)) {
                        write!(f, "({item})")?;
                    } else {
                        write!(f, "{item}")?;
                    }
                }
                Ok(())
            }
            Self::Exists(name, domain, body) => write!(f, "exists {name} from {domain}: {body}"),
            Self::Var(name, _) => f.write_str(name),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct TypeInfo {
    pub(crate) parameters: Vec<syntax::Binder>,
    pub(crate) body: Option<syntax::TypeExpr>,
}

#[derive(Clone, Debug)]
pub(crate) struct Primitive {
    pub(crate) name: String,
    pub(crate) input: Ty,
    pub(crate) output: Ty,
    pub(crate) line: usize,
    pub(crate) description: String,
    pub(crate) substitutions: BTreeMap<String, Ty>,
}

pub(crate) struct Specification {
    pub(crate) tuple_arity: usize,
    pub(crate) types: BTreeMap<String, TypeInfo>,
    pub(crate) primitives: Vec<Primitive>,
    pub(crate) features: Vec<Primitive>,
}

pub(crate) fn elaborate(document: &syntax::Document) -> Result<Specification, ValidationError> {
    let builtins = builtin_names();
    let mut types = BTreeMap::<String, TypeInfo>::new();
    for declaration in &document.types {
        if builtins.contains(declaration.name.as_str()) {
            return Err(invalid(
                declaration.line,
                format!("built-in type '{}' cannot be redeclared", declaration.name),
            ));
        }
        if types.contains_key(&declaration.name) {
            return Err(invalid(
                declaration.line,
                format!("duplicate type declaration '{}'", declaration.name),
            ));
        }
        types.insert(declaration.name.clone(), TypeInfo {
            parameters: declaration.parameters.clone(),
            body: declaration.body.clone(),
        });
    }
    for trait_decl in &document.traits {
        if builtins.contains(trait_decl.name.as_str()) || types.contains_key(&trait_decl.name) {
            return Err(invalid(
                trait_decl.line,
                format!("duplicate or reserved type '{}'", trait_decl.name),
            ));
        }
        types.insert(trait_decl.name.clone(), TypeInfo {
            parameters: trait_decl.parameters.clone(),
            body: None,
        });
    }

    check_definition_cycles(document)?;
    let mut tuple_arity = 2;
    for declaration in &document.types {
        let info = types.get(&declaration.name).expect("type was registered");
        let environments = parameter_environments(&info.parameters, &types, declaration.line)?;
        for env in environments {
            for value in env.values() {
                tuple_arity = tuple_arity.max(max_tuple_arity(value));
            }
            if let Some(body) = &info.body {
                let body = resolve(body, &types, &env, declaration.line)?;
                tuple_arity = tuple_arity.max(max_tuple_arity(&body));
            }
        }
    }
    for declaration in &document.traits {
        parameter_environments(&declaration.parameters, &types, declaration.line)?;
    }
    let mut primitives = Vec::new();
    for function in &document.functions {
        expand_function(function, &types, &mut primitives)?;
    }
    for trait_decl in &document.traits {
        expand_trait(trait_decl, &types, &mut primitives)?;
    }
    let mut feature_names = BTreeSet::new();
    for feature in &document.features {
        if !feature_names.insert(feature.name.clone()) {
            return Err(invalid(
                feature.line,
                format!("duplicate feature '{}'", feature.name),
            ));
        }
    }
    let mut features = Vec::new();
    for feature in &document.features {
        expand_feature(feature, &types, &mut features)?;
    }
    check_overloads(&primitives)?;
    for function in primitives.iter().chain(&features) {
        tuple_arity = tuple_arity
            .max(max_tuple_arity(&function.input))
            .max(max_tuple_arity(&function.output));
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

fn expand_function(
    function: &syntax::FunctionDecl,
    types: &BTreeMap<String, TypeInfo>,
    out: &mut Vec<Primitive>,
) -> Result<(), ValidationError> {
    for env in parameter_environments(&function.parameters, types, function.line)? {
        let input = resolve(&function.input, types, &env, function.line)?;
        let output = resolve(&function.output, types, &env, function.line)?;
        out.push(Primitive {
            name: function.name.clone(),
            input,
            output,
            line: function.line,
            description: function.description.clone(),
            substitutions: env.clone(),
        });
    }
    Ok(())
}

fn expand_feature(
    feature: &syntax::FeatureDecl,
    types: &BTreeMap<String, TypeInfo>,
    out: &mut Vec<Primitive>,
) -> Result<(), ValidationError> {
    for env in parameter_environments(&feature.parameters, types, feature.line)? {
        out.push(Primitive {
            name: feature.name.clone(),
            input: resolve(&feature.input, types, &env, feature.line)?,
            output: resolve(&feature.output, types, &env, feature.line)?,
            line: feature.line,
            description: feature.description.clone(),
            substitutions: env.clone(),
        });
    }
    Ok(())
}

fn expand_trait(
    trait_decl: &syntax::TraitDecl,
    types: &BTreeMap<String, TypeInfo>,
    out: &mut Vec<Primitive>,
) -> Result<(), ValidationError> {
    for trait_env in parameter_environments(&trait_decl.parameters, types, trait_decl.line)? {
        let receiver_args = trait_decl
            .parameters
            .iter()
            .filter_map(|binder| trait_env.get(&binder.name).cloned())
            .collect::<Vec<_>>();
        let receiver = Ty::Named(trait_decl.name.clone(), receiver_args);
        for member in &trait_decl.members {
            for member_env in parameter_environments_with_parent(
                &member.parameters,
                types,
                &trait_env,
                member.line,
            )? {
                let member_input = resolve(&member.input, types, &member_env, member.line)?;
                let output = resolve(&member.output, types, &member_env, member.line)?;
                let input = match member_input {
                    Ty::Unit => receiver.clone(),
                    Ty::Product(items) => {
                        let mut tuple = vec![receiver.clone()];
                        tuple.extend(items);
                        Ty::Product(tuple)
                    }
                    other => Ty::Product(vec![receiver.clone(), other]),
                };
                out.push(Primitive {
                    name: format!("{}.{}", trait_decl.name, member.name),
                    input,
                    output,
                    line: member.line,
                    description: member.description.clone(),
                    substitutions: member_env.clone(),
                });
            }
        }
    }
    Ok(())
}

pub(crate) fn parameter_environments(
    parameters: &[syntax::Binder],
    types: &BTreeMap<String, TypeInfo>,
    line: usize,
) -> Result<Vec<BTreeMap<String, Ty>>, ValidationError> {
    parameter_environments_with_parent(parameters, types, &BTreeMap::new(), line)
}

fn parameter_environments_with_parent(
    parameters: &[syntax::Binder],
    types: &BTreeMap<String, TypeInfo>,
    parent: &BTreeMap<String, Ty>,
    line: usize,
) -> Result<Vec<BTreeMap<String, Ty>>, ValidationError> {
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
        let domain = resolve(&binder.domain, types, &BTreeMap::new(), line)?;
        let variants = outer_variants(&domain, types);
        if variants.is_empty() {
            return Err(invalid(
                line,
                format!("type parameter '{}' has an empty domain", binder.name),
            ));
        }
        let mut next = Vec::new();
        for env in &envs {
            for variant in &variants {
                let mut extended = env.clone();
                extended.insert(binder.name.clone(), variant.clone());
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

pub(crate) fn resolve(
    expr: &syntax::TypeExpr,
    types: &BTreeMap<String, TypeInfo>,
    env: &BTreeMap<String, Ty>,
    line: usize,
) -> Result<Ty, ValidationError> {
    match expr {
        syntax::TypeExpr::Name(name, args) => {
            if let Some(value) = env.get(name) {
                if !args.is_empty() {
                    return Err(invalid(
                        line,
                        format!("type parameter '{name}' cannot have arguments"),
                    ));
                }
                return Ok(value.clone());
            }
            let resolved_args = args
                .iter()
                .map(|arg| resolve(arg, types, env, line))
                .collect::<Result<Vec<_>, _>>()?;
            match name.as_str() {
                "List" | "Set" if resolved_args.len() == 1 => {
                    if name == "List" {
                        Ok(Ty::List(Box::new(resolved_args[0].clone())))
                    } else {
                        Ok(Ty::Set(Box::new(resolved_args[0].clone())))
                    }
                }
                "Map" if resolved_args.len() == 2 => Ok(Ty::Map(
                    Box::new(resolved_args[0].clone()),
                    Box::new(resolved_args[1].clone()),
                )),
                "List" | "Set" | "Map" => Err(invalid(line, format!("wrong arity for {name}"))),
                "Bytes" if resolved_args.is_empty() => {
                    Ok(Ty::Named("Bytes".to_owned(), Vec::new()))
                }
                name if builtin_names().contains(name) && resolved_args.is_empty() => {
                    Ok(Ty::Named(name.to_owned(), Vec::new()))
                }
                name if builtin_names().contains(name) => Err(invalid(
                    line,
                    format!("built-in type {name} does not take arguments"),
                )),
                _ => {
                    let info = types
                        .get(name)
                        .ok_or_else(|| invalid(line, format!("unknown type '{name}'")))?;
                    if info.parameters.len() != resolved_args.len() {
                        return Err(invalid(
                            line,
                            format!(
                                "type '{name}' expects {} argument(s), got {}",
                                info.parameters.len(),
                                resolved_args.len()
                            ),
                        ));
                    }
                    for (binder, arg) in info.parameters.iter().zip(&resolved_args) {
                        let domain = resolve(&binder.domain, types, &BTreeMap::new(), line)?;
                        let permitted = outer_variants(&domain, types);
                        let valid = match arg {
                            Ty::Var(_, witnesses) => {
                                witnesses.iter().all(|w| permitted.contains(w))
                            }
                            _ => permitted.contains(arg),
                        };
                        if !valid {
                            return Err(invalid(
                                line,
                                format!(
                                    "type argument {arg} is outside the domain of {name}<{}>",
                                    binder.name
                                ),
                            ));
                        }
                    }
                    Ok(Ty::Named(name.to_owned(), resolved_args))
                }
            }
        }
        syntax::TypeExpr::Sum(items) => {
            let mut variants = Vec::new();
            for item in items {
                match resolve(item, types, env, line)? {
                    Ty::Sum(nested) => variants.extend(nested),
                    other => variants.push(other),
                }
            }
            variants.sort();
            variants.dedup();
            if variants.len() == 1 {
                Ok(variants.remove(0))
            } else {
                Ok(Ty::Sum(variants))
            }
        }
        syntax::TypeExpr::Product(items) if items.is_empty() => Ok(Ty::Unit),
        syntax::TypeExpr::Product(items) => Ok(Ty::Product(
            items
                .iter()
                .map(|item| resolve(item, types, env, line))
                .collect::<Result<_, _>>()?,
        )),
        syntax::TypeExpr::Exists(binder, body) => {
            let domain = resolve(&binder.domain, types, &BTreeMap::new(), line)?;
            let variants = outer_variants(&domain, types);
            if variants.is_empty() {
                return Err(invalid(line, "existential domain is empty"));
            }
            let mut nested = env.clone();
            if env.contains_key(&binder.name) {
                return Err(invalid(
                    line,
                    "existential binder shadows an outer parameter",
                ));
            }
            let canonical = format!(
                "T{}",
                env.values().filter(|t| matches!(t, Ty::Var(_, _))).count()
            );
            nested.insert(binder.name.clone(), Ty::Var(canonical.clone(), variants));
            let body = resolve(body, types, &nested, line)?;
            Ok(Ty::Exists(canonical, Box::new(domain), Box::new(body)))
        }
    }
}

pub(crate) fn outer_variants(ty: &Ty, types: &BTreeMap<String, TypeInfo>) -> Vec<Ty> {
    match ty {
        Ty::Sum(items) => items.clone(),
        Ty::Named(name, args) => {
            if name == "Bytes" {
                return vec![ty.clone()];
            }
            if let Some(info) = types.get(name) {
                if let Some(body) = &info.body {
                    let env = info
                        .parameters
                        .iter()
                        .zip(args)
                        .map(|(binder, arg)| (binder.name.clone(), arg.clone()))
                        .collect();
                    if let Ok(Ty::Sum(items)) = resolve(body, types, &env, 0) {
                        return items;
                    }
                }
            }
            vec![ty.clone()]
        }
        _ => vec![ty.clone()],
    }
}

fn check_overloads(primitives: &[Primitive]) -> Result<(), ValidationError> {
    let mut by_name = BTreeMap::<&str, Vec<&Primitive>>::new();
    for primitive in primitives {
        by_name.entry(&primitive.name).or_default().push(primitive);
    }
    for (name, declarations) in by_name {
        for left in 0..declarations.len() {
            for right in left + 1..declarations.len() {
                if let Some(witness) =
                    overlap_witness(&declarations[left].input, &declarations[right].input)
                {
                    return Err(invalid(
                        declarations[right].line,
                        format!(
                            "ambiguous overload '{name}': input {} (line {}) overlaps input {} (line {}); common input: {witness}",
                            declarations[left].input,
                            declarations[left].line,
                            declarations[right].input,
                            declarations[right].line
                        ),
                    ));
                }
            }
        }
    }
    Ok(())
}

fn overlap_witness(left: &Ty, right: &Ty) -> Option<Ty> {
    match (left, right) {
        (Ty::Sum(items), other) | (other, Ty::Sum(items)) => {
            items.iter().find_map(|item| overlap_witness(item, other))
        }
        (Ty::Product(a), Ty::Product(b)) if a.len() == b.len() => a
            .iter()
            .zip(b)
            .map(|(a, b)| overlap_witness(a, b))
            .collect::<Option<Vec<_>>>()
            .map(Ty::Product),
        _ if left == right => Some(left.clone()),
        _ => None,
    }
}

pub(crate) fn explicit_shape(ty: &Ty, types: &BTreeMap<String, TypeInfo>) -> Ty {
    match ty {
        Ty::Named(name, args) => {
            if name == "Bytes" {
                return Ty::List(Box::new(Ty::Named("Byte".to_owned(), Vec::new())));
            }
            types
                .get(name)
                .and_then(|info| {
                    info.body.as_ref().and_then(|body| {
                        let env = info
                            .parameters
                            .iter()
                            .zip(args)
                            .map(|(b, a)| (b.name.clone(), a.clone()))
                            .collect();
                        resolve(body, types, &env, 0).ok()
                    })
                })
                .unwrap_or_else(|| ty.clone())
        }
        _ => ty.clone(),
    }
}

pub(crate) fn source_variants(ty: &Ty, types: &BTreeMap<String, TypeInfo>) -> BTreeSet<Ty> {
    match ty {
        Ty::Sum(items) => items.iter().cloned().collect(),
        Ty::Named(name, args) => {
            if let Some(info) = types.get(name) {
                if let Some(body) = &info.body {
                    let env = info
                        .parameters
                        .iter()
                        .zip(args)
                        .map(|(b, a)| (b.name.clone(), a.clone()))
                        .collect();
                    if let Ok(Ty::Sum(items)) = resolve(body, types, &env, 0) {
                        return items.into_iter().collect();
                    }
                }
            }
            [ty.clone()].into_iter().collect()
        }
        _ => [ty.clone()].into_iter().collect(),
    }
}

pub(crate) fn handled_variants(ty: &Ty) -> BTreeSet<Ty> {
    match ty {
        Ty::Sum(items) => items.iter().cloned().collect(),
        _ => [ty.clone()].into_iter().collect(),
    }
}

pub(crate) fn union_type(items: Vec<Ty>) -> Ty {
    let mut flat = Vec::new();
    for item in items {
        match item {
            Ty::Sum(inner) => flat.extend(inner),
            other => flat.push(other),
        }
    }
    flat.sort();
    flat.dedup();
    if flat.len() == 1 {
        flat.remove(0)
    } else {
        Ty::Sum(flat)
    }
}

pub(crate) fn type_depth(ty: &Ty) -> usize {
    match ty {
        Ty::Unit | Ty::Named(_, _) | Ty::Var(_, _) | Ty::Exists(_, _, _) => 0,
        Ty::Sum(items) => items.iter().map(type_depth).max().unwrap_or(0),
        Ty::List(item) | Ty::Set(item) => 1 + type_depth(item),
        Ty::Map(key, value) => 1 + type_depth(key).max(type_depth(value)),
        Ty::Product(items) => 1 + items.iter().map(type_depth).max().unwrap_or(0),
    }
}

pub(crate) fn collect_type(ty: &Ty, out: &mut BTreeSet<Ty>) {
    if !out.insert(ty.clone()) {
        return;
    }
    match ty {
        Ty::Named(_, args) => {
            for arg in args {
                collect_type(arg, out);
            }
        }
        Ty::List(item) | Ty::Set(item) => collect_type(item, out),
        Ty::Map(k, v) => {
            collect_type(k, out);
            collect_type(v, out);
        }
        Ty::Product(items) | Ty::Sum(items) => {
            for item in items {
                collect_type(item, out);
            }
        }
        Ty::Exists(name, domain, body) => {
            collect_type(domain, out);
            // The witness is opaque at runtime. This only adds ground type nodes;
            // it does not introduce package construction or elimination.
            match find_variable(body, name) {
                Some(Ty::Var(_, witnesses)) => {
                    for witness in witnesses {
                        collect_type(&substitute(body, name, &witness), out);
                    }
                }
                None => collect_type(body, out),
                _ => unreachable!("find_variable returns only variable nodes"),
            }
        }
        Ty::Unit | Ty::Var(_, _) => {}
    }
}

pub(crate) fn accepts(contract: &Ty, supplied: &Ty) -> bool {
    if contract == supplied {
        return true;
    }
    match (contract, supplied) {
        (Ty::Sum(_), Ty::Sum(items)) => items.iter().all(|i| accepts(contract, i)),
        (Ty::Sum(items), other) => items.iter().any(|i| accepts(i, other)),
        (Ty::Product(a), Ty::Product(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| accepts(a, b))
        }
        _ => false,
    }
}

fn find_variable(ty: &Ty, name: &str) -> Option<Ty> {
    match ty {
        Ty::Var(n, _) if n == name => Some(ty.clone()),
        Ty::Named(_, a) | Ty::Product(a) | Ty::Sum(a) => {
            a.iter().find_map(|t| find_variable(t, name))
        }
        Ty::List(a) | Ty::Set(a) => find_variable(a, name),
        Ty::Map(a, b) => find_variable(a, name).or_else(|| find_variable(b, name)),
        Ty::Exists(_, _, body) => find_variable(body, name),
        _ => None,
    }
}

fn substitute(ty: &Ty, name: &str, value: &Ty) -> Ty {
    match ty {
        Ty::Var(n, _) if n == name => value.clone(),
        Ty::Named(n, a) => Ty::Named(
            n.clone(),
            a.iter().map(|t| substitute(t, name, value)).collect(),
        ),
        Ty::Product(a) => Ty::Product(a.iter().map(|t| substitute(t, name, value)).collect()),
        Ty::Sum(a) => union_type(a.iter().map(|t| substitute(t, name, value)).collect()),
        Ty::List(a) => Ty::List(Box::new(substitute(a, name, value))),
        Ty::Set(a) => Ty::Set(Box::new(substitute(a, name, value))),
        Ty::Map(a, b) => Ty::Map(
            Box::new(substitute(a, name, value)),
            Box::new(substitute(b, name, value)),
        ),
        Ty::Exists(n, d, b) => {
            Ty::Exists(n.clone(), d.clone(), Box::new(substitute(b, name, value)))
        }
        _ => ty.clone(),
    }
}

fn max_tuple_arity(ty: &Ty) -> usize {
    match ty {
        Ty::Product(items) => items
            .len()
            .max(items.iter().map(max_tuple_arity).max().unwrap_or(0)),
        Ty::Named(_, items) | Ty::Sum(items) | Ty::Var(_, items) => {
            items.iter().map(max_tuple_arity).max().unwrap_or(0)
        }
        Ty::List(item) | Ty::Set(item) => max_tuple_arity(item),
        Ty::Map(a, b) | Ty::Exists(_, a, b) => max_tuple_arity(a).max(max_tuple_arity(b)),
        Ty::Unit => 0,
    }
}
