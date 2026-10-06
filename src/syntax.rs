use std::{fmt, ops::Range};

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

/// Original UTF-8 text and the byte ranges of its preprocessed physical lines.
/// Own the input `String`; line views borrow this object, so moving it needs
/// no pointer fixups and never copies the source buffer.
#[derive(Debug)]
pub struct SourceText {
    /// Original text, never rewritten while its line ranges are in use.
    text: String,
    /// Indentation and content ranges for every physical line, including comments.
    lines: Vec<LineSpan>,
}

/// Byte ranges within one source buffer; no line text is copied or stored twice.
#[derive(Debug)]
struct LineSpan {
    /// Exact leading spaces or tabs, compared within a trait block.
    indent: Range<usize>,
    /// Declaration or semantic-description text after trimming and comment removal.
    text: Range<usize>,
    /// Whether this line contributes an attached semantic description.
    is_doc: bool,
}

/// Borrowed view of a preprocessed physical line in a `SourceText`.
/// All string slices point into the original source buffer.
#[derive(Clone, Copy, Debug)]
pub struct SourceLine<'a> {
    /// One-based physical line number before preprocessing.
    pub number: usize,
    /// Exact leading spaces or tabs, compared within a trait block.
    pub indent: &'a str,
    /// Declaration text or semantic description without its leading `///`.
    pub text: &'a str,
    /// Whether this line contributes to an attached semantic description.
    pub is_doc: bool,
}

impl SourceText {
    /// Index physical lines without copying their indentation or content.
    /// Preserve CRLF line numbers and empty descriptions, remove ordinary comments,
    /// and reject mixed spaces/tabs only on significant lines. Every stored byte
    /// range lies on UTF-8 boundaries in the unchanged original buffer.
    pub fn new(text: String) -> Result<Self, ParseError> {
        let mut lines = Vec::new();
        let mut offset = 0;
        for (index, physical) in text.split_inclusive('\n').enumerate() {
            let raw = physical.strip_suffix('\n').unwrap_or(physical);
            let raw = raw.strip_suffix('\r').unwrap_or(raw);
            let indent_bytes = raw.len() - raw.trim_start_matches([' ', '\t']).len();
            let indent = &raw[..indent_bytes];
            let trimmed = raw[indent_bytes..].trim_end();
            let is_ignored =
                trimmed.is_empty() || (trimmed.starts_with("//") && !trimmed.starts_with("///"));
            if !is_ignored && indent.contains(' ') && indent.contains('\t') {
                return Err(ParseError::new(
                    index + 1,
                    1,
                    "do not mix spaces and tabs in indentation",
                ));
            }
            let (content, prefix_bytes, is_doc) = match trimmed.strip_prefix("///") {
                Some(doc) => (doc, 3, true),
                None => (
                    trimmed
                        .split_once("//")
                        .map_or(trimmed, |(before, _)| before),
                    0,
                    false,
                ),
            };
            let leading_bytes = content.len() - content.trim_start().len();
            let start = offset + indent_bytes + prefix_bytes + leading_bytes;
            lines.push(LineSpan {
                indent: offset..offset + indent_bytes,
                text: start..start + content.trim().len(),
                is_doc,
            });
            offset += physical.len();
        }
        Ok(Self { text, lines })
    }

    /// Number of physical lines, using the same trailing-newline convention as `str::lines`.
    pub fn line_count(&self) -> usize {
        self.lines.len()
    }

    /// View one zero-based physical line; its number remains one-based.
    pub fn line(&self, index: usize) -> Option<SourceLine<'_>> {
        self.lines.get(index).map(|span| SourceLine {
            number: index + 1,
            indent: &self.text[span.indent.clone()],
            text: &self.text[span.text.clone()],
            is_doc: span.is_doc,
        })
    }

    /// Parse the ordered sections into an AST, borrowing line views during parsing.
    /// Attach descriptions and check trait indentation and section placement;
    /// name resolution and finite-domain validation are deferred to elaboration.
    /// AST names and joined descriptions are owned independently of this buffer.
    pub fn parse(&self) -> Result<Document, ParseError> {
        let mut section = 0_u8;
        let mut pending_doc = Vec::<&str>::new();
        let mut document = Document {
            types: Vec::new(),
            functions: Vec::new(),
            traits: Vec::new(),
            features: Vec::new(),
        };
        let mut index = 0;

        while index < self.line_count() {
            let line = self.line(index).expect("index is within the line count");
            index += 1;
            if line.text.trim().is_empty() && !line.is_doc {
                continue;
            }
            if !line.indent.is_empty() {
                return Err(ParseError::new(
                    line.number,
                    1,
                    "unexpected indentation outside a trait",
                ));
            }
            if line.is_doc {
                pending_doc.push(line.text);
                continue;
            }
            match line.text.trim() {
                "DEFINITIONS:" if section == 0 => {
                    reject_pending_description(&pending_doc, line.number)?;
                    section = 1;
                    continue;
                }
                "FEATURES:" if section == 1 => {
                    reject_pending_description(&pending_doc, line.number)?;
                    section = 2;
                    continue;
                }
                "DEFINITIONS:" | "FEATURES:" => {
                    return Err(ParseError::new(
                        line.number,
                        1,
                        "section is duplicated or out of order",
                    ));
                }
                _ => {}
            }
            if section == 0 {
                return Err(ParseError::new(
                    line.number,
                    1,
                    "expected DEFINITIONS: section",
                ));
            }

            let description = std::mem::take(&mut pending_doc).join("\n");
            if section == 1 && is_trait_header(line.text, line.number)? {
                let header = parse_header(line.text, line.number)?;
                let mut members = Vec::new();
                let mut trait_indent = None;
                while index < self.line_count() {
                    let member_line = self.line(index).expect("index is within the line count");
                    if member_line.text.trim().is_empty() && !member_line.is_doc {
                        index += 1;
                        continue;
                    }
                    if member_line.indent.is_empty() {
                        break;
                    }
                    let expected = trait_indent.get_or_insert(member_line.indent);
                    if member_line.indent != *expected {
                        return Err(ParseError::new(
                            member_line.number,
                            1,
                            "trait members must use consistent indentation",
                        ));
                    }
                    if member_line.is_doc {
                        pending_doc.push(member_line.text);
                        index += 1;
                        continue;
                    }
                    let member_description = std::mem::take(&mut pending_doc).join("\n");
                    members.push(
                        parse_member(member_line.text, member_line.number, member_description)
                            .map_err(|mut error| {
                                error.column += member_line.indent.len();
                                error
                            })?,
                    );
                    index += 1;
                }
                reject_pending_description(&pending_doc, line.number)?;
                if members.is_empty() {
                    return Err(ParseError::new(
                        line.number,
                        1,
                        "a trait must contain at least one member",
                    ));
                }
                document.traits.push(TraitDecl {
                    name: header.name,
                    parameters: header.parameters,
                    members,
                    description,
                    line: line.number,
                });
                continue;
            }

            if section == 1 {
                match parse_definition(line.text, line.number, description)? {
                    Definition::Type(item) => document.types.push(item),
                    Definition::Function(item) => document.functions.push(item),
                }
            } else {
                document
                    .features
                    .push(parse_feature(line.text, line.number, description)?);
            }
        }

        if section == 0 {
            return Err(ParseError::new(1, 1, "missing DEFINITIONS: section"));
        }
        if section != 2 {
            return Err(ParseError::new(
                self.line_count().max(1),
                1,
                "missing FEATURES: section",
            ));
        }
        if !pending_doc.is_empty() {
            return Err(ParseError::new(
                self.line_count().max(1),
                1,
                "description is not attached to a declaration",
            ));
        }
        Ok(document)
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
    if cursor == tokens.len() {
        if name.contains('.') {
            return Err(ParseError::new(
                line_no,
                1,
                "type names cannot be qualified",
            ));
        }
        return Ok(Definition::Type(TypeDecl {
            name,
            parameters,
            body: None,
            description,
            line: line_no,
        }));
    }
    if consume(&tokens, &mut cursor, TokenKind::Equal) {
        if name.contains('.') {
            return Err(ParseError::new(
                line_no,
                1,
                "type names cannot be qualified",
            ));
        }
        let body = parse_type_until_end(&tokens[cursor..], line_no)?;
        return Ok(Definition::Type(TypeDecl {
            name,
            parameters,
            body: Some(body),
            description,
            line: line_no,
        }));
    }
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
    if parser.cursor != tokens.len() {
        return Err(ParseError::new(
            line,
            tokens[parser.cursor].column,
            "unexpected token after type expression",
        ));
    }
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
        if self.peek_ident("exists") {
            self.cursor += 1;
            let name = self.take_name()?;
            self.expect_ident("from")?;
            let domain = self.parse_sum_until_colon()?;
            self.expect(TokenKind::Colon)?;
            let body = self.parse_sum()?;
            return Ok(TypeExpr::Exists(
                Box::new(Binder { name, domain }),
                Box::new(body),
            ));
        }
        match self.peek_kind() {
            Some(TokenKind::LParen) => self.parse_product(),
            Some(TokenKind::Ident(_)) => self.parse_named(),
            Some(_) => Err(ParseError::new(
                self.line,
                self.tokens[self.cursor].column,
                "expected a type",
            )),
            None => Err(ParseError::new(self.line, 1, "expected a type")),
        }
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
        let token = self
            .tokens
            .get(self.cursor)
            .ok_or_else(|| ParseError::new(self.line, 1, "expected identifier"))?;
        if let TokenKind::Ident(name) = &token.kind {
            reject_reserved(name, self.line, token.column)?;
            self.cursor += 1;
            Ok(name.clone())
        } else {
            Err(ParseError::new(
                self.line,
                token.column,
                "expected identifier",
            ))
        }
    }

    fn expect_ident(&mut self, expected: &str) -> Result<(), ParseError> {
        if self.peek_ident(expected) {
            self.cursor += 1;
            Ok(())
        } else {
            Err(ParseError::new(
                self.line,
                self.tokens.get(self.cursor).map_or(1, |token| token.column),
                format!("expected {expected}"),
            ))
        }
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
        if self.consume(kind) {
            Ok(())
        } else {
            Err(ParseError::new(
                self.line,
                self.tokens.get(self.cursor).map_or(1, |token| token.column),
                "unexpected token",
            ))
        }
    }
}

fn take_ident(tokens: &[Token], cursor: &mut usize, line: usize) -> Result<String, ParseError> {
    let token = tokens
        .get(*cursor)
        .ok_or_else(|| ParseError::new(line, 1, "expected identifier"))?;
    if let TokenKind::Ident(name) = &token.kind {
        reject_reserved(name, line, token.column)?;
        *cursor += 1;
        Ok(name.clone())
    } else {
        Err(ParseError::new(line, token.column, "expected identifier"))
    }
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
    match tokens.get(*cursor).map(|token| &token.kind) {
        Some(TokenKind::Ident(name)) if name == expected => {
            *cursor += 1;
            Ok(())
        }
        Some(token) => Err(ParseError::new(
            line,
            tokens[*cursor].column,
            format!("expected {expected}, found {token:?}"),
        )),
        None => Err(ParseError::new(line, 1, format!("expected {expected}"))),
    }
}

fn expect(
    tokens: &[Token],
    cursor: &mut usize,
    expected: TokenKind,
    line: usize,
) -> Result<(), ParseError> {
    if tokens
        .get(*cursor)
        .is_some_and(|token| token.kind == expected)
    {
        *cursor += 1;
        Ok(())
    } else {
        Err(ParseError::new(
            line,
            tokens.get(*cursor).map_or(1, |token| token.column),
            format!("expected {expected:?}"),
        ))
    }
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
    if cursor == tokens.len() {
        Ok(())
    } else {
        Err(ParseError::new(
            line,
            tokens[cursor].column,
            "unexpected trailing tokens",
        ))
    }
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

fn reject_reserved(name: &str, line: usize, column: usize) -> Result<(), ParseError> {
    if matches!(name, "from" | "exists" | "DEFINITIONS" | "FEATURES") {
        Err(ParseError::new(
            line,
            column,
            format!("'{name}' is a reserved word"),
        ))
    } else {
        Ok(())
    }
}
fn reject_pending_description(pending: &[&str], line: usize) -> Result<(), ParseError> {
    if pending.is_empty() {
        Ok(())
    } else {
        Err(ParseError::new(
            line,
            1,
            "description is not attached to a declaration",
        ))
    }
}

#[cfg(test)]
mod tests;
