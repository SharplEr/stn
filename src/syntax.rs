use std::{
    fmt,
    iter::{Enumerate, FusedIterator},
    str::Lines,
};

/// Parsed specification before name resolution, normalization, or specialization.
/// Semantic descriptions and declaration lines are retained for later diagnostics.
#[derive(Clone, Debug)]
pub struct Document {
    /// Opaque and structurally defined types from `DEFINITIONS`.
    pub types: Vec<TypeDecl>,
    /// Standalone function declarations, including qualified static methods.
    pub functions: Vec<FunctionDecl>,
    /// Trait declarations whose members will become receiver-taking functions.
    pub traits: Vec<TraitDecl>,
    /// Goals from `FEATURES`; these are not available function declarations.
    pub features: Vec<FeatureDecl>,
}

/// Source declaration of an opaque nominal type or a nominal structural definition.
#[derive(Clone, Debug)]
pub struct TypeDecl {
    /// Unqualified nominal type name.
    pub name: String,
    /// Finite family parameters, in source order.
    pub parameters: Vec<Binder>,
    /// Right-hand side of `=`, or absence for an opaque declaration.
    pub body: Option<TypeExpr>,
    /// Attached `///` lines, joined with newlines.
    pub description: String,
    /// One-based declaration line in the original source.
    pub line: usize,
}

/// Source signature of a standalone morphism or feature before parameter expansion.
/// A qualified name alone does not introduce an implicit receiver.
/// Its containing `Document` section determines whether it is a morphism or a goal.
#[derive(Clone, Debug)]
pub struct FunctionDecl {
    /// Function or feature name, possibly qualified with dots.
    pub name: String,
    /// Finite parameters local to this signature.
    pub parameters: Vec<Binder>,
    /// Explicit input expression to the left of `->`.
    pub input: TypeExpr,
    /// Explicit output expression to the right of `->`.
    pub output: TypeExpr,
    /// Attached semantic description, preserved without interpreting its prose.
    pub description: String,
    /// One-based declaration line in the original source.
    pub line: usize,
}

/// Source trait block declaring a nominal receiver and a set of member signatures.
/// It describes callable structure without declaring concrete implementations.
#[derive(Clone, Debug)]
pub struct TraitDecl {
    /// Nominal receiver name introduced by the trait.
    pub name: String,
    /// Finite parameters visible in every member signature.
    pub parameters: Vec<Binder>,
    /// Members in source order, with field syntax already expanded.
    pub members: Vec<MemberDecl>,
    /// Semantic description attached to the trait header.
    pub description: String,
    /// One-based line of the trait header.
    pub line: usize,
}

/// Parsed trait member before adding its receiver argument.
/// Field syntax `name: T` is represented as an explicit `() -> T` signature.
#[derive(Clone, Debug)]
pub struct MemberDecl {
    /// Unqualified member name, later prefixed with its trait name.
    pub name: String,
    /// Finite parameters declared on this member in addition to trait parameters.
    pub parameters: Vec<Binder>,
    /// Member input excluding the receiver; an empty product for field syntax.
    pub input: TypeExpr,
    /// Member output expression, including any declared error alternatives.
    pub output: TypeExpr,
    /// Semantic description attached to this member.
    pub description: String,
    /// One-based line of the member declaration.
    pub line: usize,
}

/// Source feature signature to be expanded into ground proof-search goals.
/// Functions and features have identical syntax, so they share a record type.
/// Features stay in `Document::features`, have unique names, and never become
/// available morphisms, including after a successful proof.
pub type FeatureDecl = FunctionDecl;

/// A `name from domain` binder used by finite parameters and existential types.
/// Elaboration resolves the domain and checks that it supplies permitted choices.
#[derive(Clone, Debug)]
pub struct Binder {
    /// Parameter name scoped over the declaration or existential body.
    pub name: String,
    /// Source expression describing the finite choice domain.
    pub domain: TypeExpr,
}

/// Type-expression syntax before semantic names and parameter bindings are resolved.
/// Unlike the semantic type model, sums retain their source order and duplicates.
#[derive(Clone, Debug)]
pub enum TypeExpr {
    /// A type reference and its optional family or collection arguments.
    Name(String, Vec<TypeExpr>),
    /// Alternatives separated by `|`, to be normalized during elaboration.
    Sum(Vec<TypeExpr>),
    /// Ordered tuple components; an empty vector represents `()`.
    Product(Vec<TypeExpr>),
    /// An existential binder and the body over which its name is scoped.
    Exists(Box<Binder>, Box<TypeExpr>),
}

/// Lexer or parser diagnostic with a one-based source position.
#[derive(Debug)]
pub struct ParseError {
    /// Physical source line containing the error.
    pub line: usize,
    /// Character column within the source line, counting a tab as one character.
    pub column: usize,
    /// Explanation of the unexpected input or missing grammar element.
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.line, self.column, self.message)
    }
}
impl std::error::Error for ParseError {}

impl ParseError {
    fn new(line: usize, column: usize, message: impl Into<String>) -> Self {
        Self {
            line,
            column,
            message: message.into(),
        }
    }

    /// Construct the diagnostic for a description without a following declaration.
    fn unattached_description(line: usize) -> Self {
        Self::new(line, 1, "description is not attached to a declaration")
    }

    /// Restore the original column after parsing an indentation-free line view.
    fn with_indent(mut self, indent: &str) -> Self {
        self.column += indent.len();
        self
    }
}

impl fmt::Display for TypeExpr {
    /// Render parsed type syntax with product parentheses and grouped existential
    /// sum alternatives, so the printed expression preserves binder scope.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Name(name, args) if args.is_empty() => f.write_str(name),
            Self::Name(name, args) => {
                write!(f, "{name}<")?;
                for (index, arg) in args.iter().enumerate() {
                    if index != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                f.write_str(">")
            }
            Self::Sum(items) => {
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        f.write_str(" | ")?;
                    }
                    if matches!(item, Self::Exists(_, _)) {
                        write!(f, "({item})")?;
                    } else {
                        write!(f, "{item}")?;
                    }
                }
                Ok(())
            }
            Self::Product(items) => {
                f.write_str("(")?;
                for (index, item) in items.iter().enumerate() {
                    if index != 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_str(")")
            }
            Self::Exists(binder, body) => {
                write!(f, "exists {} from {}: {}", binder.name, binder.domain, body)
            }
        }
    }
}

/// Token categories for declaration and type-expression parsing.
/// Keywords are lexed as identifiers and interpreted or rejected by the parser.
#[derive(Clone, Debug, PartialEq)]
enum TokenKind {
    Ident(String),
    Colon,
    Equal,
    Pipe,
    Arrow,
    Dot,
    Less,
    Greater,
    Comma,
    LParen,
    RParen,
}

/// One token and its character position within the text passed to the lexer.
/// Member diagnostics add the removed indentation to recover source columns.
#[derive(Clone, Debug)]
struct Token {
    /// Identifier text or punctuation category.
    kind: TokenKind,
    /// One-based character column in the lexed line text.
    column: usize,
}

/// Owner of the original UTF-8 source buffer, without any precomputed line index.
/// Iterators and parser state borrow its slices; the returned AST owns its strings.
#[derive(Debug)]
pub struct SourceText {
    /// Original text, moved into this object without copying or rewriting its buffer.
    text: String,
}

/// Borrowed view of a significant physical source line.
/// All text and indentation slices point into the original source buffer.
#[derive(Clone, Copy, Debug)]
pub struct SourceLine<'a> {
    /// One-based physical line number, including skipped blank and comment lines.
    pub number: usize,
    /// Exact leading spaces or tabs, compared within a trait block.
    pub indent: &'a str,
    /// Trimmed declaration or description text, without an ordinary comment or `///` prefix.
    pub text: &'a str,
    /// Whether this line contributes an attached semantic description.
    pub is_doc: bool,
}

impl SourceLine<'_> {
    /// Validate the indentation required by the current document state.
    fn check_indent(&self, indent: &str) -> Result<(), ParseError> {
        if self.indent != indent {
            let message = if indent.is_empty() {
                "unexpected indentation outside a trait"
            } else {
                "trait members must use consistent indentation"
            };
            return Err(ParseError::new(self.number, 1, message));
        }
        Ok(())
    }
}

/// Lazy preprocessing over borrowed physical lines, using constant iterator storage.
/// Skip ordinary comments and blank lines, retain semantic descriptions, and
/// validate indentation prefixes only when the consumer requests the next item.
#[derive(Debug)]
pub struct SourceLines<'a> {
    /// Physical lines with their original zero-based indices, before any filtering.
    physical: Enumerate<Lines<'a>>,
    /// Diagnostic position of the last consumed physical line, or one for empty input.
    eof_line: usize,
}

impl SourceLines<'_> {
    /// Last consumed physical line; after exhaustion this is the EOF diagnostic position.
    pub fn eof_line(&self) -> usize {
        self.eof_line
    }
}

impl<'a> Iterator for SourceLines<'a> {
    type Item = Result<SourceLine<'a>, ParseError>;

    fn next(&mut self) -> Option<Self::Item> {
        for (index, raw) in self.physical.by_ref() {
            self.eof_line = index + 1;
            let raw = raw.strip_suffix('\r').unwrap_or(raw);
            let indent_bytes = raw.len() - raw.trim_start_matches([' ', '\t']).len();
            let indent = &raw[..indent_bytes];
            let trimmed = raw[indent_bytes..].trim_end();
            let (text, is_doc) = match trimmed.strip_prefix("///") {
                Some(doc) => (doc.trim(), true),
                None => (
                    trimmed
                        .split_once("//")
                        .map_or(trimmed, |(before, _)| before)
                        .trim(),
                    false,
                ),
            };
            if text.is_empty() && !is_doc {
                continue;
            }
            let line = SourceLine {
                number: index + 1,
                indent,
                text,
                is_doc,
            };
            return Some(check_indent_prefix(indent, trimmed, line.number).map(|()| line));
        }
        None
    }
}

impl FusedIterator for SourceLines<'_> {}

impl SourceText {
    /// Take ownership without scanning the source or copying its buffer.
    pub fn new(text: String) -> Self {
        Self { text }
    }

    /// Create a fresh lazy iterator over significant lines, borrowing the source text.
    pub fn lines(&self) -> SourceLines<'_> {
        SourceLines {
            physical: self.text.lines().enumerate(),
            eof_line: 1,
        }
    }

    /// Feed significant lines into the document automaton, then validate its final state.
    /// Preprocessing and parsing follow source order; malformed input stops consumption.
    /// AST names and joined descriptions are owned independently of this buffer.
    pub fn parse(&self) -> Result<Document, ParseError> {
        let mut lines = self.lines();
        let mut parser = DocumentParser::new();
        for line in &mut lines {
            parser = parser.accept(line?)?;
        }
        parser.finish(lines.eof_line())
    }
}

/// Required document sections, with their source spelling and missing-header location.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Section {
    /// Declarations of types, morphisms, and traits; required at the document start.
    Definitions,
    /// Feature goals; required after all definitions.
    Features,
}

impl Section {
    /// Exact spelling of the section's standalone header.
    fn header(self) -> &'static str {
        match self {
            Self::Definitions => "DEFINITIONS:",
            Self::Features => "FEATURES:",
        }
    }

    /// Recognize a header using the same spellings as expected-header diagnostics.
    fn from_header(text: &str) -> Option<Self> {
        [Self::Definitions, Self::Features]
            .into_iter()
            .find(|section| section.header() == text)
    }

    /// Diagnose a missing opening section at the start, or a missing final section at EOF.
    fn missing_line(self, eof_line: usize) -> usize {
        match self {
            Self::Definitions => 1,
            Self::Features => eof_line,
        }
    }

    /// Construct the diagnostic when EOF is reached before this required section.
    fn missing_error(self, eof_line: usize) -> ParseError {
        ParseError::new(
            self.missing_line(eof_line),
            1,
            format!("missing {} section", self.header()),
        )
    }

    /// Check a present header; all unexpected-header diagnostics are built separately.
    fn check_header(self, line: SourceLine<'_>) -> Result<(), ParseError> {
        if line.text != self.header() {
            return Err(self.unexpected_error(line));
        }
        Ok(())
    }

    /// Distinguish a reordered section from a declaration where a header was required.
    fn unexpected_error(self, line: SourceLine<'_>) -> ParseError {
        let message = match Self::from_header(line.text) {
            Some(_) => "section is duplicated or out of order".to_owned(),
            None => format!("expected {} section", self.header()),
        };
        ParseError::new(line.number, 1, message)
    }

    /// Reject a section header encountered where only declarations are allowed.
    fn reject_header(line: SourceLine<'_>) -> Result<(), ParseError> {
        if Self::from_header(line.text).is_some() {
            return Err(ParseError::new(
                line.number,
                1,
                "section is duplicated or out of order",
            ));
        }
        Ok(())
    }
}

/// One significant line together with its attached, independently owned description.
/// The declaration text and indentation still borrow the original source buffer.
struct DescribedLine<'a> {
    /// Physical source position, indentation, and declaration text.
    line: SourceLine<'a>,
    /// Consecutive semantic description lines, joined once for the AST.
    description: String,
}

impl DescribedLine<'_> {
    /// Parse an indented member and attach original-column context to syntax errors.
    fn parse_member(self) -> Result<MemberDecl, ParseError> {
        parse_member(self.line.text, self.line.number, self.description)
            .map_err(|error| error.with_indent(self.line.indent))
    }
}

/// Current state of the document automaton; only trait state owns an unfinished block.
/// Every accepted declaration determines the state for the next input line.
enum State<'a> {
    /// The opening DEFINITIONS header has not yet been accepted.
    ExpectDefinitions,
    /// Accept type, function, and trait declarations or the FEATURES header.
    Definitions,
    /// Accumulate a trait's members until the next unindented line.
    Trait(TraitBuilder<'a>),
    /// Accept feature signatures until the end of input.
    Features,
}

impl<'a> State<'a> {
    /// Check indentation before processing a description or declaration.
    /// The first significant trait line fixes its block prefix.
    fn check_indent(&mut self, line: SourceLine<'a>) -> Result<(), ParseError> {
        match self {
            Self::Trait(builder) => builder.check_indent(line),
            _ => line.check_indent(""),
        }
    }

    /// Accept a non-description entry and return the next state.
    /// Append completed declarations directly to their corresponding AST collections.
    fn accept_entry(
        self,
        entry: DescribedLine<'a>,
        document: &mut Document,
    ) -> Result<Self, ParseError> {
        match self {
            Self::ExpectDefinitions => {
                Section::Definitions.check_header(entry.line)?;
                Ok(Self::Definitions)
            }
            Self::Definitions => match Section::from_header(entry.line.text) {
                Some(Section::Features) => Ok(Self::Features),
                Some(_) => Err(Section::Features.unexpected_error(entry.line)),
                None if is_trait_header(entry.line.text, entry.line.number)? => {
                    Ok(Self::Trait(TraitBuilder::new(entry)?))
                }
                None => {
                    match parse_definition(entry.line.text, entry.line.number, entry.description)? {
                        Definition::Type(item) => document.types.push(item),
                        Definition::Function(item) => document.functions.push(item),
                    }
                    Ok(Self::Definitions)
                }
            },
            Self::Trait(mut builder) => {
                builder.add_member(entry)?;
                Ok(Self::Trait(builder))
            }
            Self::Features => {
                Section::reject_header(entry.line)?;
                document.features.push(parse_feature(
                    entry.line.text,
                    entry.line.number,
                    entry.description,
                )?);
                Ok(Self::Features)
            }
        }
    }

    /// Close an active trait at dedent or EOF; all other states pass through unchanged.
    /// The caller can then feed the same dedented line into the Definitions state.
    fn finish_trait(
        self,
        document: &mut Document,
        has_pending_description: bool,
    ) -> Result<Self, ParseError> {
        match self {
            Self::Trait(builder) => {
                document
                    .traits
                    .push(builder.finish(has_pending_description)?);
                Ok(Self::Definitions)
            }
            state => Ok(state),
        }
    }

    /// Verify that both required headers have been seen when input is exhausted.
    fn check_finished(&self, eof_line: usize) -> Result<(), ParseError> {
        match self {
            Self::ExpectDefinitions => Err(Section::Definitions.missing_error(eof_line)),
            Self::Definitions | Self::Trait(_) => Err(Section::Features.missing_error(eof_line)),
            Self::Features => Ok(()),
        }
    }
}

/// Accumulator for one trait declaration while its member lines are being accepted.
struct TraitBuilder<'a> {
    /// Owned trait header, semantic description, and members accumulated in source order.
    declaration: TraitDecl,
    /// First member or description line's exact indentation, borrowed from the source.
    indent: Option<&'a str>,
}

impl<'a> TraitBuilder<'a> {
    /// Parse the header and begin an empty member block without copying its source slices.
    fn new(entry: DescribedLine<'a>) -> Result<Self, ParseError> {
        let header = parse_header(entry.line.text, entry.line.number)?;
        Ok(Self {
            declaration: TraitDecl {
                name: header.name,
                parameters: header.parameters,
                members: Vec::new(),
                description: entry.description,
                line: entry.line.number,
            },
            indent: None,
        })
    }

    /// Fix the first block prefix and reject later changes, including on descriptions.
    fn check_indent(&mut self, line: SourceLine<'a>) -> Result<(), ParseError> {
        let indent = self.indent.get_or_insert(line.indent);
        line.check_indent(indent)
    }

    /// Parse a member with original-column diagnostics and append it to this trait.
    fn add_member(&mut self, entry: DescribedLine<'a>) -> Result<(), ParseError> {
        self.declaration.members.push(entry.parse_member()?);
        Ok(())
    }

    /// Require a nonempty member block with no unattached description before emitting it.
    fn finish(self, has_pending_description: bool) -> Result<TraitDecl, ParseError> {
        if has_pending_description {
            return Err(ParseError::unattached_description(self.declaration.line));
        }
        if self.declaration.members.is_empty() {
            return Err(ParseError::new(
                self.declaration.line,
                1,
                "a trait must contain at least one member",
            ));
        }
        Ok(self.declaration)
    }
}

/// Stateful consumer of preprocessed lines, independent of the source iterator.
/// State transitions move unfinished traits; borrowed descriptions are joined once
/// when attached, while completed declarations accumulate in the owned AST.
struct DocumentParser<'a> {
    /// Grammar state expected to consume the next significant line.
    state: State<'a>,
    /// Semantic description lines waiting for a declaration at the current indentation.
    descriptions: Vec<&'a str>,
    /// Completed declarations, grouped by their role in the specification.
    document: Document,
}

impl<'a> DocumentParser<'a> {
    /// Begin before the required opening header, with no accumulated declarations.
    fn new() -> Self {
        Self {
            state: State::ExpectDefinitions,
            descriptions: Vec::new(),
            document: Document {
                types: Vec::new(),
                functions: Vec::new(),
                traits: Vec::new(),
                features: Vec::new(),
            },
        }
    }

    /// Consume one line and return the updated parser without copying accumulated data.
    /// At dedent, finish the trait before processing this same line at top level.
    /// Descriptions retain source slices; declarations receive one joined string.
    fn accept(mut self, line: SourceLine<'a>) -> Result<Self, ParseError> {
        if line.indent.is_empty() {
            self.state = self
                .state
                .finish_trait(&mut self.document, !self.descriptions.is_empty())?;
        }
        self.state.check_indent(line)?;
        if line.is_doc {
            self.descriptions.push(line.text);
        } else {
            if !self.descriptions.is_empty()
                && line.indent.is_empty()
                && Section::from_header(line.text).is_some()
            {
                return Err(ParseError::unattached_description(line.number));
            }
            let entry = DescribedLine {
                line,
                description: self.descriptions.join("\n"),
            };
            self.descriptions.clear();
            self.state = self.state.accept_entry(entry, &mut self.document)?;
        }
        Ok(self)
    }

    /// Finalize the last trait, check pending descriptions and required sections, then emit AST.
    /// The iterator supplies the physical EOF line, including skipped trailing comments.
    fn finish(mut self, eof_line: usize) -> Result<Document, ParseError> {
        self.state = self
            .state
            .finish_trait(&mut self.document, !self.descriptions.is_empty())?;
        if !self.descriptions.is_empty() {
            return Err(ParseError::unattached_description(eof_line));
        }
        self.state.check_finished(eof_line)?;
        Ok(self.document)
    }
}

fn is_trait_header(line: &str, line_no: usize) -> Result<bool, ParseError> {
    let tokens = tokenize(line, line_no)?;
    Ok(matches!(
        tokens.last().map(|token| &token.kind),
        Some(TokenKind::Colon)
    ))
}

/// Parsed trait header before collecting its indented members.
struct Header {
    /// Nominal receiver name introduced by the header.
    name: String,
    /// Finite trait parameters shared by all members.
    parameters: Vec<Binder>,
}

/// Parse a trait's unqualified name and optional finite binders, requiring a final
/// colon and no member signature or other trailing tokens on the header line.
fn parse_header(line: &str, line_no: usize) -> Result<Header, ParseError> {
    let tokens = tokenize(line, line_no)?;
    let mut cursor = 0;
    let name = take_ident(&tokens, &mut cursor, line_no)?;
    let parameters = parse_optional_binders(&tokens, &mut cursor, line_no)?;
    expect(&tokens, &mut cursor, TokenKind::Colon, line_no)?;
    ensure_end(&tokens, cursor, line_no)?;
    Ok(Header { name, parameters })
}

/// Result of parsing a non-trait declaration in `DEFINITIONS`.
/// The syntax after its name distinguishes a type from a function signature.
enum Definition {
    Type(TypeDecl),
    Function(FunctionDecl),
}

/// Distinguish an opaque type, nominal structural definition, and free function
/// from the tokens following its name and binders. Qualified names are allowed
/// only for functions; signatures split at an arrow outside nested constructors.
fn parse_definition(
    line: &str,
    line_no: usize,
    description: String,
) -> Result<Definition, ParseError> {
    let tokens = tokenize(line, line_no)?;
    let mut cursor = 0;
    let name = take_qualified_name(&tokens, &mut cursor, line_no)?;
    let parameters = parse_optional_binders(&tokens, &mut cursor, line_no)?;
    match tokens.get(cursor).map(|token| &token.kind) {
        None | Some(TokenKind::Equal) => {
            check_type_name(&name, line_no)?;
            let body = if consume(&tokens, &mut cursor, TokenKind::Equal) {
                Some(parse_type_until_end(&tokens[cursor..], line_no)?)
            } else {
                None
            };
            Ok(Definition::Type(TypeDecl {
                name,
                parameters,
                body,
                description,
                line: line_no,
            }))
        }
        _ => {
            expect(&tokens, &mut cursor, TokenKind::Colon, line_no)?;
            let arrow = find_top_level_arrow(&tokens, cursor)
                .ok_or_else(|| ParseError::new(line_no, 1, "function signature is missing ->"))?;
            let input = parse_type_until_end(&tokens[cursor..arrow], line_no)?;
            let output = parse_type_until_end(&tokens[arrow + 1..], line_no)?;
            Ok(Definition::Function(FunctionDecl {
                name,
                parameters,
                input,
                output,
                description,
                line: line_no,
            }))
        }
    }
}

/// Parse a trait member signature, interpreting a bare output type as the field
/// shorthand `() -> Output`. Receiver insertion is deferred to trait lowering.
fn parse_member(line: &str, line_no: usize, description: String) -> Result<MemberDecl, ParseError> {
    let tokens = tokenize(line, line_no)?;
    let mut cursor = 0;
    let name = take_ident(&tokens, &mut cursor, line_no)?;
    let parameters = parse_optional_binders(&tokens, &mut cursor, line_no)?;
    expect(&tokens, &mut cursor, TokenKind::Colon, line_no)?;
    let arrow = find_top_level_arrow(&tokens, cursor);
    let (input, output) = if let Some(arrow) = arrow {
        (
            parse_type_until_end(&tokens[cursor..arrow], line_no)?,
            parse_type_until_end(&tokens[arrow + 1..], line_no)?,
        )
    } else {
        (
            TypeExpr::Product(Vec::new()),
            parse_type_until_end(&tokens[cursor..], line_no)?,
        )
    };
    Ok(MemberDecl {
        name,
        parameters,
        input,
        output,
        description,
        line: line_no,
    })
}

/// Parse a named, optionally parameterized feature goal with an explicit arrow.
/// Its placement in `Document::features` keeps it a goal during elaboration.
fn parse_feature(
    line: &str,
    line_no: usize,
    description: String,
) -> Result<FeatureDecl, ParseError> {
    let tokens = tokenize(line, line_no)?;
    let mut cursor = 0;
    let name = take_qualified_name(&tokens, &mut cursor, line_no)?;
    let parameters = parse_optional_binders(&tokens, &mut cursor, line_no)?;
    expect(&tokens, &mut cursor, TokenKind::Colon, line_no)?;
    let arrow = find_top_level_arrow(&tokens, cursor)
        .ok_or_else(|| ParseError::new(line_no, 1, "feature signature is missing ->"))?;
    let input = parse_type_until_end(&tokens[cursor..arrow], line_no)?;
    let output = parse_type_until_end(&tokens[arrow + 1..], line_no)?;
    Ok(FeatureDecl {
        name,
        parameters,
        input,
        output,
        description,
        line: line_no,
    })
}

/// Parse a declaration's optional `<T from Domain, ...>` list, advancing the
/// cursor past its closing bracket. Nested type constructors belong to domains;
/// domain names and admissible witnesses are checked during elaboration.
fn parse_optional_binders(
    tokens: &[Token],
    cursor: &mut usize,
    line: usize,
) -> Result<Vec<Binder>, ParseError> {
    if !consume(tokens, cursor, TokenKind::Less) {
        return Ok(Vec::new());
    }
    let mut binders = Vec::new();
    loop {
        let name = take_ident(tokens, cursor, line)?;
        expect_ident(tokens, cursor, "from", line)?;
        let domain_start = *cursor;
        let domain_end = find_binder_end(tokens, domain_start, line)?;
        let domain = parse_type_until_end(&tokens[domain_start..domain_end], line)?;
        *cursor = domain_end;
        binders.push(Binder { name, domain });
        if consume(tokens, cursor, TokenKind::Comma) {
            continue;
        }
        expect(tokens, cursor, TokenKind::Greater, line)?;
        return Ok(binders);
    }
}

/// Locate the comma or closing angle bracket ending one binder's domain, ignoring
/// delimiters inside nested generic arguments and parenthesized expressions.
fn find_binder_end(tokens: &[Token], start: usize, line: usize) -> Result<usize, ParseError> {
    let mut depth = 0_i32;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        match token.kind {
            TokenKind::Less | TokenKind::LParen => depth += 1,
            TokenKind::Greater if depth == 0 => return Ok(index),
            TokenKind::Greater | TokenKind::RParen => depth -= 1,
            TokenKind::Comma if depth == 0 => return Ok(index),
            _ => {}
        }
        if depth < 0 {
            break;
        }
    }
    Err(ParseError::new(
        line,
        tokens.get(start).map_or(1, |token| token.column),
        "unterminated type-parameter list",
    ))
}

/// Locate a signature arrow outside generic arguments and parenthesized types.
/// The returned index separates input and output token slices for type parsing.
fn find_top_level_arrow(tokens: &[Token], start: usize) -> Option<usize> {
    let mut depth = 0_i32;
    for (index, token) in tokens.iter().enumerate().skip(start) {
        match token.kind {
            TokenKind::Less | TokenKind::LParen => depth += 1,
            TokenKind::Greater | TokenKind::RParen => depth -= 1,
            TokenKind::Arrow if depth == 0 => return Some(index),
            _ => {}
        }
    }
    None
}

/// Parse one complete type expression from a declaration-selected token slice.
/// Reject leftover tokens so a valid prefix cannot hide malformed trailing syntax.
fn parse_type_until_end(tokens: &[Token], line: usize) -> Result<TypeExpr, ParseError> {
    let mut parser = TypeParser {
        tokens,
        cursor: 0,
        line,
    };
    let ty = parser.parse_sum()?;
    parser.expect_end()?;
    Ok(ty)
}

/// Recursive descent state for one bounded slice of type-expression tokens.
/// The surrounding declaration parser selects the slice at signature delimiters.
struct TypeParser<'a> {
    /// Borrowed tokens belonging to the expression being parsed.
    tokens: &'a [Token],
    /// Index of the next token to consume.
    cursor: usize,
    /// Original physical line used by type-expression diagnostics.
    line: usize,
}

impl TypeParser<'_> {
    /// Parse the lowest-precedence `|` chain. Keep its source structure in the AST;
    /// flattening, commutativity, and duplicate elimination belong to elaboration.
    fn parse_sum(&mut self) -> Result<TypeExpr, ParseError> {
        let mut items = vec![self.parse_primary()?];
        while self.consume(TokenKind::Pipe) {
            items.push(self.parse_primary()?);
        }
        if items.len() == 1 {
            Ok(items.remove(0))
        } else {
            Ok(TypeExpr::Sum(items))
        }
    }

    /// Parse a named application, parentheses/product, or existential package.
    /// An existential body consumes a full sum, giving its binder scope over all
    /// alternatives until the surrounding expression's delimiter.
    fn parse_primary(&mut self) -> Result<TypeExpr, ParseError> {
        match self.peek_kind() {
            Some(TokenKind::Ident(name)) if name == "exists" => self.parse_existential(),
            Some(TokenKind::LParen) => self.parse_product(),
            Some(TokenKind::Ident(_)) => self.parse_named(),
            _ => Err(self.error("expected a type")),
        }
    }

    /// Parse an existential binder followed by the full sum expression in its scope.
    fn parse_existential(&mut self) -> Result<TypeExpr, ParseError> {
        self.cursor += 1;
        let name = self.take_name()?;
        self.expect_ident("from")?;
        let domain = self.parse_sum_until_colon()?;
        self.expect(TokenKind::Colon)?;
        let body = self.parse_sum()?;
        Ok(TypeExpr::Exists(
            Box::new(Binder { name, domain }),
            Box::new(body),
        ))
    }

    /// Isolate an existential's domain at the first unnested colon, then parse
    /// that slice as a complete type without consuming the binder/body separator.
    fn parse_sum_until_colon(&mut self) -> Result<TypeExpr, ParseError> {
        let start = self.cursor;
        let mut depth = 0_i32;
        while self.cursor < self.tokens.len() {
            match self.tokens[self.cursor].kind {
                TokenKind::Less | TokenKind::LParen => depth += 1,
                TokenKind::Greater | TokenKind::RParen => depth -= 1,
                TokenKind::Colon if depth == 0 => break,
                _ => {}
            }
            self.cursor += 1;
        }
        parse_type_until_end(&self.tokens[start..self.cursor], self.line)
    }

    /// Distinguish unit `()`, grouping `(T)`, and an ordered product `(T, U, ...)`.
    /// Components are full sum expressions, and nested products stay nested.
    fn parse_product(&mut self) -> Result<TypeExpr, ParseError> {
        self.cursor += 1;
        if self.consume(TokenKind::RParen) {
            return Ok(TypeExpr::Product(Vec::new()));
        }
        let first = self.parse_sum()?;
        if !self.consume(TokenKind::Comma) {
            self.expect(TokenKind::RParen)?;
            return Ok(first);
        }
        let items = self.parse_comma_separated(vec![first], TokenKind::RParen)?;
        Ok(TypeExpr::Product(items))
    }

    /// Parse a type name and optional comma-separated type arguments. Arguments
    /// can themselves be sums or nested applications; arity is checked later.
    fn parse_named(&mut self) -> Result<TypeExpr, ParseError> {
        let name = self.take_name()?;
        let args = if self.consume(TokenKind::Less) {
            self.parse_comma_separated(Vec::new(), TokenKind::Greater)?
        } else {
            Vec::new()
        };
        Ok(TypeExpr::Name(name, args))
    }

    /// Parse at least one more full type, then consume the required closing token.
    /// Products pass their already parsed first component; named applications
    /// start empty. Empty arguments and trailing commas remain syntax errors.
    fn parse_comma_separated(
        &mut self,
        mut items: Vec<TypeExpr>,
        closing: TokenKind,
    ) -> Result<Vec<TypeExpr>, ParseError> {
        loop {
            items.push(self.parse_sum()?);
            if !self.consume(TokenKind::Comma) {
                self.expect(closing)?;
                return Ok(items);
            }
        }
    }

    fn take_name(&mut self) -> Result<String, ParseError> {
        take_ident(self.tokens, &mut self.cursor, self.line)
    }

    fn expect_ident(&mut self, expected: &str) -> Result<(), ParseError> {
        if !self.peek_ident(expected) {
            return Err(self.error(format!("expected {expected}")));
        }
        self.cursor += 1;
        Ok(())
    }

    /// Construct a diagnostic at the current token, using column one at EOF.
    fn error(&self, message: impl Into<String>) -> ParseError {
        let column = self.tokens.get(self.cursor).map_or(1, |token| token.column);
        ParseError::new(self.line, column, message)
    }

    /// Require the parsed type to consume its entire token slice.
    fn expect_end(&self) -> Result<(), ParseError> {
        if self.cursor != self.tokens.len() {
            return Err(self.error("unexpected token after type expression"));
        }
        Ok(())
    }

    fn peek_ident(&self, expected: &str) -> bool {
        matches!(self.tokens.get(self.cursor).map(|token| &token.kind), Some(TokenKind::Ident(name)) if name == expected)
    }

    fn peek_kind(&self) -> Option<&TokenKind> {
        self.tokens.get(self.cursor).map(|token| &token.kind)
    }

    fn consume(&mut self, kind: TokenKind) -> bool {
        if self.peek_kind() == Some(&kind) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: TokenKind) -> Result<(), ParseError> {
        if !self.consume(kind) {
            return Err(self.error("unexpected token"));
        }
        Ok(())
    }
}

fn take_ident(tokens: &[Token], cursor: &mut usize, line: usize) -> Result<String, ParseError> {
    let token = tokens
        .get(*cursor)
        .ok_or_else(|| ParseError::new(line, 1, "expected identifier"))?;
    let TokenKind::Ident(name) = &token.kind else {
        return Err(ParseError::new(line, token.column, "expected identifier"));
    };
    reject_reserved(name, line, token.column)?;
    *cursor += 1;
    Ok(name.clone())
}

fn take_qualified_name(
    tokens: &[Token],
    cursor: &mut usize,
    line: usize,
) -> Result<String, ParseError> {
    let mut name = take_ident(tokens, cursor, line)?;
    while tokens
        .get(*cursor)
        .is_some_and(|token| token.kind == TokenKind::Dot)
    {
        *cursor += 1;
        name.push('.');
        name.push_str(&take_ident(tokens, cursor, line)?);
    }
    Ok(name)
}

fn expect_ident(
    tokens: &[Token],
    cursor: &mut usize,
    expected: &str,
    line: usize,
) -> Result<(), ParseError> {
    let token = tokens
        .get(*cursor)
        .ok_or_else(|| ParseError::new(line, 1, format!("expected {expected}")))?;
    if !matches!(&token.kind, TokenKind::Ident(name) if name == expected) {
        return Err(ParseError::new(
            line,
            token.column,
            format!("expected {expected}, found {:?}", token.kind),
        ));
    }
    *cursor += 1;
    Ok(())
}

fn expect(
    tokens: &[Token],
    cursor: &mut usize,
    expected: TokenKind,
    line: usize,
) -> Result<(), ParseError> {
    if !tokens
        .get(*cursor)
        .is_some_and(|token| token.kind == expected)
    {
        return Err(ParseError::new(
            line,
            tokens.get(*cursor).map_or(1, |token| token.column),
            format!("expected {expected:?}"),
        ));
    }
    *cursor += 1;
    Ok(())
}

fn consume(tokens: &[Token], cursor: &mut usize, expected: TokenKind) -> bool {
    if tokens
        .get(*cursor)
        .is_some_and(|token| token.kind == expected)
    {
        *cursor += 1;
        true
    } else {
        false
    }
}

fn ensure_end(tokens: &[Token], cursor: usize, line: usize) -> Result<(), ParseError> {
    if cursor != tokens.len() {
        return Err(ParseError::new(
            line,
            tokens[cursor].column,
            "unexpected trailing tokens",
        ));
    }
    Ok(())
}

/// Tokenize one comment-free declaration using ASCII identifiers, punctuation,
/// and the two-character arrow. Retain one-based character columns for syntax
/// diagnostics and reject every character not admitted by the concrete grammar.
fn tokenize(text: &str, line: usize) -> Result<Vec<Token>, ParseError> {
    let chars: Vec<char> = text.chars().collect();
    let mut tokens = Vec::new();
    let mut cursor = 0;
    while cursor < chars.len() {
        if chars[cursor].is_whitespace() {
            cursor += 1;
            continue;
        }
        let column = cursor + 1;
        let kind = match chars[cursor] {
            ':' => {
                cursor += 1;
                TokenKind::Colon
            }
            '=' => {
                cursor += 1;
                TokenKind::Equal
            }
            '|' => {
                cursor += 1;
                TokenKind::Pipe
            }
            '.' => {
                cursor += 1;
                TokenKind::Dot
            }
            '<' => {
                cursor += 1;
                TokenKind::Less
            }
            '>' => {
                cursor += 1;
                TokenKind::Greater
            }
            ',' => {
                cursor += 1;
                TokenKind::Comma
            }
            '(' => {
                cursor += 1;
                TokenKind::LParen
            }
            ')' => {
                cursor += 1;
                TokenKind::RParen
            }
            '-' if chars.get(cursor + 1) == Some(&'>') => {
                cursor += 2;
                TokenKind::Arrow
            }
            c if c == '_' || c.is_ascii_alphabetic() => {
                let start = cursor;
                cursor += 1;
                while chars
                    .get(cursor)
                    .is_some_and(|c| *c == '_' || c.is_ascii_alphanumeric())
                {
                    cursor += 1;
                }
                TokenKind::Ident(chars[start..cursor].iter().collect())
            }
            other => {
                return Err(ParseError::new(
                    line,
                    column,
                    format!("unexpected character {other:?}"),
                ));
            }
        };
        tokens.push(Token { kind, column });
    }
    Ok(tokens)
}

/// Validate significant-line prefixes while ignoring blank lines and ordinary comments.
fn check_indent_prefix(indent: &str, content: &str, line: usize) -> Result<(), ParseError> {
    let is_ignored =
        content.is_empty() || (content.starts_with("//") && !content.starts_with("///"));
    if !is_ignored && indent.contains(' ') && indent.contains('\t') {
        return Err(ParseError::new(
            line,
            1,
            "do not mix spaces and tabs in indentation",
        ));
    }
    Ok(())
}

/// Reject qualified names for nominal type declarations.
fn check_type_name(name: &str, line: usize) -> Result<(), ParseError> {
    if name.contains('.') {
        return Err(ParseError::new(line, 1, "type names cannot be qualified"));
    }
    Ok(())
}

fn reject_reserved(name: &str, line: usize, column: usize) -> Result<(), ParseError> {
    if matches!(name, "from" | "exists" | "DEFINITIONS" | "FEATURES") {
        return Err(ParseError::new(
            line,
            column,
            format!("'{name}' is a reserved word"),
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
