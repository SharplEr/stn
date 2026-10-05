use std::fmt;

#[derive(Clone, Debug)]
pub struct Document {
    pub types: Vec<TypeDecl>,
    pub functions: Vec<FunctionDecl>,
    pub traits: Vec<TraitDecl>,
    pub features: Vec<FeatureDecl>,
}

#[derive(Clone, Debug)]
pub struct TypeDecl {
    pub name: String,
    pub parameters: Vec<Binder>,
    pub body: Option<TypeExpr>,
    pub description: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct FunctionDecl {
    pub name: String,
    pub parameters: Vec<Binder>,
    pub input: TypeExpr,
    pub output: TypeExpr,
    pub description: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct TraitDecl {
    pub name: String,
    pub parameters: Vec<Binder>,
    pub members: Vec<MemberDecl>,
    pub description: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct MemberDecl {
    pub name: String,
    pub parameters: Vec<Binder>,
    pub input: TypeExpr,
    pub output: TypeExpr,
    pub description: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct FeatureDecl {
    pub name: String,
    pub parameters: Vec<Binder>,
    pub input: TypeExpr,
    pub output: TypeExpr,
    pub description: String,
    pub line: usize,
}

#[derive(Clone, Debug)]
pub struct Binder {
    pub name: String,
    pub domain: TypeExpr,
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    Name(String, Vec<TypeExpr>),
    Sum(Vec<TypeExpr>),
    Product(Vec<TypeExpr>),
    Exists(Box<Binder>, Box<TypeExpr>),
}

#[derive(Debug)]
pub struct ParseError {
    pub line: usize,
    pub column: usize,
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

#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
    column: usize,
}

#[derive(Clone, Debug)]
struct SourceLine {
    number: usize,
    indent: String,
    text: String,
    is_doc: bool,
}

pub fn parse(source: &str) -> Result<Document, ParseError> {
    let lines = source_lines(source)?;
    let mut section = 0_u8;
    let mut pending_doc = Vec::<String>::new();
    let mut document = Document {
        types: Vec::new(),
        functions: Vec::new(),
        traits: Vec::new(),
        features: Vec::new(),
    };
    let mut index = 0;

    while index < lines.len() {
        let line = &lines[index];
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
            pending_doc.push(line.text.clone());
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
        if section == 1 && is_trait_header(&line.text, line.number)? {
            let header = parse_header(&line.text, line.number)?;
            let mut members = Vec::new();
            let mut trait_indent = None;
            while index < lines.len() {
                let member_line = &lines[index];
                if member_line.text.trim().is_empty() && !member_line.is_doc {
                    index += 1;
                    continue;
                }
                if member_line.indent.is_empty() {
                    break;
                }
                let expected = trait_indent.get_or_insert_with(|| member_line.indent.clone());
                if &member_line.indent != expected {
                    return Err(ParseError::new(
                        member_line.number,
                        1,
                        "trait members must use consistent indentation",
                    ));
                }
                if member_line.is_doc {
                    pending_doc.push(member_line.text.clone());
                    index += 1;
                    continue;
                }
                let expected = trait_indent.get_or_insert_with(|| member_line.indent.clone());
                if &member_line.indent != expected {
                    return Err(ParseError::new(
                        member_line.number,
                        1,
                        "trait members must use consistent indentation",
                    ));
                }
                let member_description = std::mem::take(&mut pending_doc).join("\n");
                members.push(
                    parse_member(&member_line.text, member_line.number, member_description)
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
            match parse_definition(&line.text, line.number, description)? {
                Definition::Type(item) => document.types.push(item),
                Definition::Function(item) => document.functions.push(item),
            }
        } else {
            document
                .features
                .push(parse_feature(&line.text, line.number, description)?);
        }
    }

    if section == 0 {
        return Err(ParseError::new(1, 1, "missing DEFINITIONS: section"));
    }
    if section != 2 {
        return Err(ParseError::new(
            source.lines().count().max(1),
            1,
            "missing FEATURES: section",
        ));
    }
    if !pending_doc.is_empty() {
        return Err(ParseError::new(
            source.lines().count().max(1),
            1,
            "description is not attached to a declaration",
        ));
    }
    Ok(document)
}

fn source_lines(source: &str) -> Result<Vec<SourceLine>, ParseError> {
    let mut result = Vec::new();
    for (index, raw) in source.lines().enumerate() {
        let line_number = index + 1;
        let without_cr = raw.strip_suffix('\r').unwrap_or(raw);
        let indent_bytes = without_cr
            .char_indices()
            .take_while(|(_, ch)| *ch == ' ' || *ch == '\t')
            .map(|(offset, ch)| offset + ch.len_utf8())
            .last()
            .unwrap_or(0);
        let indent = without_cr[..indent_bytes].to_owned();
        let trimmed = without_cr[indent_bytes..].trim_end();
        let is_ignored =
            trimmed.is_empty() || (trimmed.starts_with("//") && !trimmed.starts_with("///"));
        if !is_ignored && indent.contains(' ') && indent.contains('\t') {
            return Err(ParseError::new(
                line_number,
                1,
                "do not mix spaces and tabs in indentation",
            ));
        }
        if trimmed.is_empty() {
            result.push(SourceLine {
                number: line_number,
                indent,
                text: String::new(),
                is_doc: false,
            });
            continue;
        }
        if let Some(doc) = trimmed.strip_prefix("///") {
            result.push(SourceLine {
                number: line_number,
                indent,
                text: doc.trim().to_owned(),
                is_doc: true,
            });
            continue;
        }
        let content = trimmed
            .split_once("//")
            .map_or(trimmed, |(before, _)| before)
            .trim_end();
        if content.trim().is_empty() {
            result.push(SourceLine {
                number: line_number,
                indent,
                text: String::new(),
                is_doc: false,
            });
        } else {
            result.push(SourceLine {
                number: line_number,
                indent,
                text: content.trim().to_owned(),
                is_doc: false,
            });
        }
    }
    Ok(result)
}

fn is_trait_header(line: &str, line_no: usize) -> Result<bool, ParseError> {
    let tokens = tokenize(line, line_no)?;
    Ok(matches!(
        tokens.last().map(|token| &token.kind),
        Some(TokenKind::Colon)
    ))
}

struct Header {
    name: String,
    parameters: Vec<Binder>,
}

fn parse_header(line: &str, line_no: usize) -> Result<Header, ParseError> {
    let tokens = tokenize(line, line_no)?;
    let mut cursor = 0;
    let name = take_ident(&tokens, &mut cursor, line_no)?;
    let parameters = parse_optional_binders(&tokens, &mut cursor, line_no)?;
    expect(&tokens, &mut cursor, TokenKind::Colon, line_no)?;
    ensure_end(&tokens, cursor, line_no)?;
    Ok(Header { name, parameters })
}

enum Definition {
    Type(TypeDecl),
    Function(FunctionDecl),
}

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

struct TypeParser<'a> {
    tokens: &'a [Token],
    cursor: usize,
    line: usize,
}

impl TypeParser<'_> {
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
        let mut items = vec![first];
        loop {
            items.push(self.parse_sum()?);
            if self.consume(TokenKind::Comma) {
                continue;
            }
            self.expect(TokenKind::RParen)?;
            break;
        }
        Ok(TypeExpr::Product(items))
    }

    fn parse_named(&mut self) -> Result<TypeExpr, ParseError> {
        let name = self.take_name()?;
        let mut args = Vec::new();
        if self.consume(TokenKind::Less) {
            loop {
                args.push(self.parse_sum()?);
                if self.consume(TokenKind::Comma) {
                    continue;
                }
                self.expect(TokenKind::Greater)?;
                break;
            }
        }
        Ok(TypeExpr::Name(name, args))
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
fn reject_pending_description(pending: &[String], line: usize) -> Result<(), ParseError> {
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
