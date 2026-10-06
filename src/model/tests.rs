//! Type translation helpers for the independent test-only proof checker.
use super::{Type, TypeId, TypeStore};
use std::collections::HashMap;

#[test]
fn elaboration_moves_metadata_and_copies_only_additional_specializations() {
    let document = crate::syntax::SourceText::new(
        "DEFINITIONS:\nA\nB\nKinds = A | B\n/// Function description\nf<T from Kinds>: T -> T\nFEATURES:\n/// Feature description\nsame<T from Kinds>: T -> T\n".to_owned(),
    )
    .parse()
    .unwrap();
    let function_name = document.functions[0].name.as_ptr();
    let function_description = document.functions[0].description.as_ptr();
    let feature_name = document.features[0].name.as_ptr();
    let feature_description = document.features[0].description.as_ptr();
    let specification = super::elaborate(document).unwrap();

    for (signatures, name, description) in [
        (
            &specification.primitives,
            function_name,
            function_description,
        ),
        (&specification.features, feature_name, feature_description),
    ] {
        assert_eq!(signatures.len(), 2);
        assert_ne!(signatures[0].input, signatures[1].input);
        assert!(
            signatures
                .iter()
                .all(|signature| signature.input == signature.output)
        );
        assert_eq!(
            signatures
                .iter()
                .filter(|signature| signature.name.as_ptr() == name)
                .count(),
            1,
        );
        assert_eq!(
            signatures
                .iter()
                .filter(|signature| signature.description.as_ptr() == description)
                .count(),
            1,
        );
    }
}

impl TypeStore {
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
