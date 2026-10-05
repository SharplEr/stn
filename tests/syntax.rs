use stn_validator::{
    ValidationOptions,
    syntax::{TypeExpr, parse},
    validate_source,
};

#[test]
fn preserves_unicode_descriptions_and_ignores_regular_comments() {
    let ast = parse("DEFINITIONS:\r\n/// Порядковый номер\r\n// regular comment\r\nDocId // inline\r\nReader:\r\n\t/// Документ\r\n\tvalue: DocId\r\nFEATURES:\r\n/// Feature description\r\nf: Reader -> DocId\r\n").unwrap();
    assert_eq!(ast.types[0].description, "Порядковый номер");
    assert_eq!(ast.traits[0].members[0].description, "Документ");
    assert_eq!(ast.features[0].description, "Feature description");
}

#[test]
fn existential_scope_and_product_grouping_are_unambiguous() {
    let ast = parse("DEFINITIONS:\nA = exists T from S: F<T> | None\nB = (exists T from S: F<T>) | None\nC = (Bar | Baz, Size)\nFEATURES:\n").unwrap();
    assert!(matches!(ast.types[0].body, Some(TypeExpr::Exists(_, _))));
    assert!(matches!(ast.types[1].body, Some(TypeExpr::Sum(_))));
    assert!(matches!(ast.types[2].body,Some(TypeExpr::Product(ref v)) if v.len()==2));
}

#[test]
fn malformed_documents_have_line_and_column() {
    for source in [
        "FEATURES:\nDEFINITIONS:\n",
        "DEFINITIONS:\nA\n",
        "DEFINITIONS:\nA,\nFEATURES:\n",
        "DEFINITIONS:\nA = (B,)\nFEATURES:\n",
        "DEFINITIONS:\nA = List<>\nFEATURES:\n",
        "DEFINITIONS:\nR:\n    a: A\n  b: B\nFEATURES:\n",
        "DEFINITIONS:\nR:\n \ta: A\nFEATURES:\n",
        "DEFINITIONS:\nR:\n\ta: A\n b: B\nFEATURES:\n",
        "DEFINITIONS:\n/// orphan\nFEATURES:\n",
        "DEFINITIONS:\nR:\n    a: A\n    /// orphan\nFEATURES:\n",
        "DEFINITIONS:\nfrom\nFEATURES:\n",
        "DEFINITIONS:\nA = Foo.Bar\nFEATURES:\n",
        "DEFINITIONS:\nA\nFEATURES:\nf: A -> @\n",
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.line > 0 && error.column > 0);
    }
}

#[test]
fn semantic_errors_are_caught_in_unused_declarations() {
    for defs in [
        "A = Unknown",
        "A\nA",
        "String",
        "A = List<String, Byte>",
        "A\nB\nKinds = A | B\nF<T from Kinds>\nBad = F<String>",
        "A\nF<T from A, U from T>",
        "A\nR<T from A>:\n    m<T from A>: T",
        "A\nBad = exists T from A: List<Unknown>",
    ] {
        assert!(
            validate_source(
                &format!("DEFINITIONS:\n{defs}\nFEATURES:\n"),
                &ValidationOptions::default()
            )
            .is_err(),
            "{defs}"
        );
    }
}

#[test]
fn indentation_on_ordinary_comments_is_ignored_and_empty_description_lines_survive() {
    let ast = parse(
        "DEFINITIONS:\n/// first\n///\n/// last\n \t// ordinary comment\n \t\nA\nFEATURES:\n",
    )
    .unwrap();
    assert_eq!(ast.types[0].description, "first\n\nlast");
}
