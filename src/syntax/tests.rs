//! Parser tests and source inspection helpers, compiled only under `cfg(test)`.
use super::{Document, ParseError, SourceText, TypeExpr};
use crate::{ValidationOptions, validate_source};

impl SourceText {
    /// Borrow the complete original text, including whitespace and comments.
    fn as_str(&self) -> &str {
        &self.text
    }
}

/// Parse an owned source buffer through lazy line preprocessing and the document automaton.
/// Construct `SourceText` explicitly to iterate its line views or parse repeatedly.
fn parse(source: String) -> Result<Document, ParseError> {
    SourceText::new(source).parse()
}

#[test]
fn line_views_borrow_owned_unicode_text_and_preserve_crlf_positions() {
    let text = "DEFINITIONS:\r\n///  Документ  \r\nReader: // inline\r\n\tvalue: String\r\nFEATURES:\r\nf: Reader -> String\r\n";
    let text = text.to_owned();
    let original_buffer = text.as_ptr();
    let source = SourceText::new(text);
    let text = source.as_str();
    assert_eq!(source.as_str().as_ptr(), original_buffer);
    let mut lines = source.lines();
    assert_eq!(lines.next().unwrap().unwrap().text, "DEFINITIONS:");
    let doc = lines.next().unwrap().unwrap();
    assert_eq!(doc.number, 2);
    assert_eq!(doc.text, "Документ");
    assert!(doc.is_doc);
    assert_eq!(
        doc.text.as_ptr(),
        text[text.find("Документ").unwrap()..].as_ptr()
    );
    assert_eq!(lines.next().unwrap().unwrap().text, "Reader:");
    let member = lines.next().unwrap().unwrap();
    assert_eq!(member.number, 4);
    assert_eq!(member.indent, "\t");
    assert_eq!(member.text, "value: String");
    assert_eq!(
        member.indent.as_ptr(),
        text[text.find("\tvalue").unwrap()..].as_ptr()
    );
    assert_eq!(lines.next().unwrap().unwrap().text, "FEATURES:");
    assert_eq!(lines.next().unwrap().unwrap().text, "f: Reader -> String");
    assert!(lines.next().is_none());
    assert_eq!(lines.eof_line(), 6);
    let document = source.parse().unwrap();
    assert_eq!(document.traits[0].members[0].line, 4);
    assert_eq!(document.types.len(), 0);
    assert_eq!(document.traits[0].description, "Документ");
}

#[test]
fn owned_source_moves_without_copying_the_buffer_and_ast_outlives_it() {
    let text = String::from("DEFINITIONS:\n/// first\n///\n/// last\nA\nFEATURES:\nsame: A -> A\n");
    let original_buffer = text.as_ptr();
    let source = SourceText::new(text);
    let mut sources = Vec::new();
    sources.push(source);
    let source = sources.pop().unwrap();
    assert_eq!(source.as_str().as_ptr(), original_buffer);
    assert_eq!(source.lines().nth(4).unwrap().unwrap().text, "A");
    let document = source.parse().unwrap();
    drop(source);
    assert_eq!(document.types[0].description, "first\n\nlast");
    assert_eq!(document.features[0].name, "same");
}

#[test]
fn lazy_sources_follow_physical_line_conventions_at_boundaries() {
    for text in [
        "",
        "\n",
        "\r\n",
        "///\n",
        "///",
        "// ignored",
        "\n\n",
        "A\r",
    ] {
        let source = SourceText::new(text.to_owned());
        let mut lines = source.lines();
        for line in &mut lines {
            let line = line.unwrap();
            assert!(line.number <= text.lines().count());
            assert!(line.text.is_empty() || line.text == "A");
        }
        assert_eq!(lines.eof_line(), text.lines().count().max(1), "{text:?}");
        assert!(lines.next().is_none());
    }
}

#[test]
fn line_iterator_filters_lazily_and_retains_physical_positions() {
    let source =
        SourceText::new("DEFINITIONS:\n \t// ignored\n\n///\nA\n \tBad\n// trailing\n".to_owned());
    let mut lines = source.lines();
    assert_eq!(lines.eof_line(), 1);
    assert_eq!(lines.next().unwrap().unwrap().number, 1);
    let description = lines.next().unwrap().unwrap();
    assert_eq!(description.number, 4);
    assert!(description.is_doc);
    assert!(description.text.is_empty());
    assert_eq!(lines.eof_line(), 4);
    assert_eq!(lines.next().unwrap().unwrap().text, "A");
    let error = lines.next().unwrap().unwrap_err();
    assert_eq!((error.line, error.column), (6, 1));
    assert_eq!(error.message, "do not mix spaces and tabs in indentation");
    assert!(lines.next().is_none());
    assert_eq!(lines.eof_line(), 7);
    assert!(lines.next().is_none());
}

#[test]
fn parsing_stops_before_a_later_line_preprocessing_error() {
    let error = parse("A\n \tBad\n".to_owned()).unwrap_err();
    assert_eq!((error.line, error.column), (1, 1));
    assert_eq!(error.message, "expected DEFINITIONS: section");
}

#[test]
fn dedent_finishes_each_trait_and_accepts_the_same_line_in_definitions() {
    let ast = parse(
        concat!(
            "DEFINITIONS:\nA\n",
            "/// Reader contract\nReader:\n",
            "   /// Member contract\n// ignored without dedenting\n   value: A\n",
            "/// Writer contract\nWriter:\n  append: A -> ()\n",
            "FEATURES:\n/// Goal contract\nf: Reader -> A\n",
        )
        .to_owned(),
    )
    .unwrap();
    assert_eq!(ast.traits.len(), 2);
    assert_eq!(ast.traits[0].name, "Reader");
    assert_eq!(ast.traits[0].description, "Reader contract");
    assert_eq!(ast.traits[0].members[0].description, "Member contract");
    assert_eq!(ast.traits[1].name, "Writer");
    assert_eq!(ast.traits[1].description, "Writer contract");
    assert_eq!(ast.traits[1].members[0].name, "append");
    assert_eq!(ast.features.len(), 1);
    assert_eq!(ast.features[0].description, "Goal contract");
}

#[test]
fn preserves_unicode_descriptions_and_ignores_regular_comments() {
    let ast = parse("DEFINITIONS:\r\n/// Порядковый номер\r\n// regular comment\r\nDocId // inline\r\nReader:\r\n\t/// Документ\r\n\tvalue: DocId\r\nFEATURES:\r\n/// Feature description\r\nf: Reader -> DocId\r\n".to_owned()).unwrap();
    assert_eq!(ast.types[0].description, "Порядковый номер");
    assert_eq!(ast.traits[0].members[0].description, "Документ");
    assert_eq!(ast.features[0].description, "Feature description");
}

#[test]
fn existential_scope_and_product_grouping_are_unambiguous() {
    let ast = parse("DEFINITIONS:\nA = exists T from S: F<T> | None\nB = (exists T from S: F<T>) | None\nC = (Bar | Baz, Size)\nFEATURES:\n".to_owned()).unwrap();
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
        let error = parse(source.to_owned()).unwrap_err();
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
                "input",
                format!("DEFINITIONS:\n{defs}\nFEATURES:\n"),
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
        "DEFINITIONS:\n/// first\n///\n/// last\n \t// ordinary comment\n \t\nA\nFEATURES:\n"
            .to_owned(),
    )
    .unwrap();
    assert_eq!(ast.types[0].description, "first\n\nlast");
}

#[test]
fn descriptions_stay_with_their_declarations_across_block_boundaries() {
    let ast = parse(
        concat!(
            "DEFINITIONS:\n",
            "/// Receiver\nReader:\n",
            "    /// First\n    // ignored\n\n    first: String\n",
            "    /// Second\n    second: String\n",
            "// ignored\n/// Value type\nValue\n",
            "FEATURES:\n/// Goal\nf: Reader -> String\n",
        )
        .to_owned(),
    )
    .unwrap();
    assert_eq!(ast.traits[0].description, "Receiver");
    assert_eq!(ast.traits[0].members.len(), 2);
    assert_eq!(ast.traits[0].members[0].description, "First");
    assert_eq!(ast.traits[0].members[1].description, "Second");
    assert_eq!(ast.types[0].name, "Value");
    assert_eq!(ast.types[0].description, "Value type");
    assert_eq!(ast.features[0].description, "Goal");
}

#[test]
fn section_and_trait_boundaries_report_their_source_positions() {
    for (source, line, column, message) in [
        ("", 1, 1, "missing DEFINITIONS: section"),
        ("A\n", 1, 1, "expected DEFINITIONS: section"),
        ("FEATURES:\n", 1, 1, "section is duplicated or out of order"),
        (
            "DEFINITIONS:\nDEFINITIONS:\nFEATURES:\n",
            2,
            1,
            "section is duplicated or out of order",
        ),
        (
            "DEFINITIONS:\nFEATURES:\nFEATURES:\n",
            3,
            1,
            "section is duplicated or out of order",
        ),
        ("DEFINITIONS:\nA\n", 2, 1, "missing FEATURES: section"),
        (
            "DEFINITIONS:\nA\n// trailing comment\n\n",
            4,
            1,
            "missing FEATURES: section",
        ),
        (
            "DEFINITIONS:\nReader:\n",
            2,
            1,
            "a trait must contain at least one member",
        ),
        (
            "DEFINITIONS:\nReader:\n    value: String\n// trailing\n",
            4,
            1,
            "missing FEATURES: section",
        ),
        (
            "DEFINITIONS:\nReader:\n    /// orphan\n",
            2,
            1,
            "description is not attached to a declaration",
        ),
        (
            "/// orphan\n// trailing\n\n",
            3,
            1,
            "description is not attached to a declaration",
        ),
        (
            "DEFINITIONS:\n/// orphan\n// trailing\n",
            3,
            1,
            "description is not attached to a declaration",
        ),
        (
            "DEFINITIONS:\nFEATURES:\n/// orphan\n// trailing\n\n",
            5,
            1,
            "description is not attached to a declaration",
        ),
        (
            "DEFINITIONS:\nReader:\nFEATURES:\n",
            2,
            1,
            "a trait must contain at least one member",
        ),
        (
            "DEFINITIONS:\nReader:\n    value: String\n    /// orphan\nA\nFEATURES:\n",
            2,
            1,
            "description is not attached to a declaration",
        ),
        (
            "DEFINITIONS:\nReader:\n    value: String\n  /// wrong indent\nFEATURES:\n",
            4,
            1,
            "trait members must use consistent indentation",
        ),
        (
            "DEFINITIONS:\nReader:\n    value: @\nFEATURES:\n",
            3,
            12,
            "unexpected character '@'",
        ),
        (
            "DEFINITIONS:\n/// orphan\nFEATURES:\n",
            3,
            1,
            "description is not attached to a declaration",
        ),
        (
            "DEFINITIONS:\nFEATURES:\n/// orphan\n",
            3,
            1,
            "description is not attached to a declaration",
        ),
    ] {
        let error = parse(source.to_owned()).unwrap_err();
        assert_eq!((error.line, error.column), (line, column), "{source:?}");
        assert_eq!(error.message, message, "{source:?}");
    }
}
