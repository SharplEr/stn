//! Parser tests and source inspection helpers, compiled only under `cfg(test)`.
use super::{Document, ParseError, SourceLine, SourceText, TypeExpr};
use crate::{ValidationOptions, validate_source};

impl SourceText {
    /// Borrow the complete original text, including whitespace and comments.
    fn as_str(&self) -> &str {
        &self.text
    }

    /// Iterate borrowed line views in their original physical order.
    fn lines(&self) -> impl ExactSizeIterator<Item = SourceLine<'_>> + DoubleEndedIterator {
        (0..self.line_count())
            .map(|index| self.line(index).expect("index is within the line count"))
    }
}

/// Parse an owned source buffer through the range-based source-line index.
/// Construct `SourceText` explicitly to retain its line views or parse repeatedly.
fn parse(source: String) -> Result<Document, ParseError> {
    SourceText::new(source)?.parse()
}

#[test]
fn line_views_borrow_owned_unicode_text_and_preserve_crlf_positions() {
    let text = "DEFINITIONS:\r\n///  Документ  \r\nReader: // inline\r\n\tvalue: String\r\nFEATURES:\r\nf: Reader -> String\r\n";
    let text = text.to_owned();
    let original_buffer = text.as_ptr();
    let source = SourceText::new(text).unwrap();
    let text = source.as_str();
    assert_eq!(source.as_str().as_ptr(), original_buffer);
    assert_eq!(source.line_count(), text.lines().count());
    assert_eq!(source.lines().len(), 6);
    assert!(source.line(6).is_none());

    let doc = source.line(1).unwrap();
    assert_eq!(doc.number, 2);
    assert_eq!(doc.text, "Документ");
    assert!(doc.is_doc);
    assert_eq!(
        doc.text.as_ptr(),
        text[text.find("Документ").unwrap()..].as_ptr()
    );

    let member = source.line(3).unwrap();
    assert_eq!(member.indent, "\t");
    assert_eq!(member.text, "value: String");
    assert_eq!(
        member.indent.as_ptr(),
        text[text.find("\tvalue").unwrap()..].as_ptr()
    );
    assert_eq!(source.line(2).unwrap().text, "Reader:");
    let document = source.parse().unwrap();
    assert_eq!(document.traits[0].members[0].line, 4);
    assert_eq!(document.types.len(), 0);
    assert_eq!(document.traits[0].description, "Документ");
}

#[test]
fn owned_source_moves_without_copying_the_buffer_and_ast_outlives_it() {
    let text = String::from("DEFINITIONS:\n/// first\n///\n/// last\nA\nFEATURES:\nsame: A -> A\n");
    let original_buffer = text.as_ptr();
    let source = SourceText::new(text).unwrap();
    let mut sources = Vec::new();
    sources.push(source);
    let source = sources.pop().unwrap();
    assert_eq!(source.as_str().as_ptr(), original_buffer);
    assert_eq!(source.line(4).unwrap().text, "A");
    let document = source.parse().unwrap();
    drop(source);
    assert_eq!(document.types[0].description, "first\n\nlast");
    assert_eq!(document.features[0].name, "same");
}

#[test]
fn indexed_sources_follow_physical_line_conventions_at_boundaries() {
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
        let source = SourceText::new(text.to_owned()).unwrap();
        assert_eq!(source.line_count(), text.lines().count(), "{text:?}");
        for line in source.lines() {
            assert!(line.number <= source.line_count());
            assert!(line.text.is_empty() || line.text == "A");
        }
    }
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
