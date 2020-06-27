//! Whitespace-sensitive lexer
//! We enforce spaces instead of tabs

use crate::error::{Span, Spanned};
use std::fmt;
use std::str::FromStr;

pub type LexResult<'i> = Result<(usize, Tok<'i>, usize), Spanned<LexError>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexError {
    /// Tabs instead of spaces
    Tabs,
    InvalidToken,
    InvalidLiteral(String),
    /// `\r` without `\n`
    CarriageReturn,
    /// An error from the parser - since `LexError` is our "user error" type for LALRPOP errors, we need to carry custom parser errors here too
    Other(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok<'i> {
    Fun,       // "fun"
    Type(u32), // "Type0"
    Int,       // "Int"
    Struct,    // "struct"
    Do,        // "do"
    The,       // "the"
    Move,      // "move"
    Of,        // "of"
    Data,      // "type" - called Data because it's not "Type"

    Colon,         // ":"
    Semi,          // ";"
    Arrow,         // "=>"
    Equals,        // "="
    Newline,       // "\n"
    LitInt(i32),   // "12"
    Name(&'i str), // "x"
    POpen,         // "("
    PClose,        // ")"
    BraceOpen,     // "{"
    BraceClose,    // "}"
    Comma,         // ","
    Dot,           // "."
    Bar,           // "|"
    Plus,          // "+"
    Minus,         // "-"
    Times,         // "*"
    Div,           // "/"

    Indent,
    Dedent,
}

trait CharExt {
    fn non_newline_whitespace(self) -> bool;
    fn is_identifier(self) -> bool;
}
impl CharExt for char {
    fn non_newline_whitespace(self) -> bool {
        self.is_whitespace() && self != '\n' && self != '\r' && self != '\t'
    }
    fn is_identifier(self) -> bool {
        self.is_alphanumeric() || self == '_'
    }
}

pub struct Lexer<'i> {
    chars: std::iter::Peekable<std::str::Chars<'i>>,
    input: &'i str,
    was_newline: bool,
    was_dedent: bool,
    indent: Vec<usize>,
    last: usize,
    pos: usize,
}

impl<'i> Lexer<'i> {
    fn save(&self) -> (usize, std::iter::Peekable<std::str::Chars<'i>>) {
        (self.pos, self.chars.clone())
    }
    fn load(&mut self, (pos, chars): (usize, std::iter::Peekable<std::str::Chars<'i>>)) {
        self.pos = pos;
        self.chars = chars;
    }

    pub fn new(input: &'i str) -> Self {
        Lexer {
            chars: input.chars().peekable(),
            input,
            was_newline: false,
            was_dedent: false,
            indent: Vec::new(),
            last: 0,
            pos: 0,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().cloned()
    }
    fn next(&mut self) -> Option<char> {
        self.pos += 1;
        self.chars.next()
    }
    fn span(&self) -> Span {
        Span(self.last, self.pos)
    }
    fn slice(&self) -> &'i str {
        &self.input[self.last..self.pos]
    }

    fn handle_indent(&mut self) -> Option<Result<Tok<'i>, LexError>> {
        let state = self.save();

        for i in self.indent.clone() {
            for _ in 0..i {
                if self.peek() == Some('\t') {
                    return Some(Err(LexError::Tabs));
                }
                if self.peek() != Some(' ') {
                    // If the line is blank, we don't care. Skip it and do the next one.
                    if self.peek() == Some('\n') {
                        self.next();
                        return self.handle_indent();
                    } else if self.peek() == Some('\r') {
                        self.next();
                        if self.next() != Some('\n') {
                            return Some(Err(LexError::CarriageReturn));
                        }
                        return self.handle_indent();
                    } else if self.peek() == Some('#') {
                        // Skip line comments
                        // eat \r here, it's always got a \n after it
                        while self.peek().map_or(false, |x| x != '\n') {
                            self.next();
                        }
                        return self.handle_indent();
                    }

                    self.indent.pop();
                    self.was_dedent = true;
                    // Start the line over so we can tell if we have another dedent after this
                    self.load(state);
                    return Some(Ok(Tok::Dedent));
                } else {
                    self.next();
                }
            }
        }

        self.was_newline = false;

        if self.peek() == Some(' ') {
            self.indent.push(0);
            while self.peek() == Some(' ') {
                self.next();
                *self.indent.last_mut().unwrap() += 1;
            }
            return Some(Ok(Tok::Indent));
        }

        if self.peek() == Some('\t') {
            return Some(Err(LexError::Tabs));
        }

        None
    }

    fn consume_whitespace(&mut self) {
        loop {
            if let Some(c) = self.peek() {
                if c == '#' {
                    // Skip line comments
                    // eat \r here, it's always got a \n after it
                    while self.peek().map_or(false, |x| x != '\n') {
                        self.next();
                    }
                }
                if !c.non_newline_whitespace() {
                    break;
                } else {
                    self.next();
                }
            } else {
                break;
            }
        }
    }

    fn lex_number(&mut self) -> Result<Tok<'i>, Spanned<LexError>> {
        Ok(loop {
            let c = self.peek();
            if c.map_or(false, |c| c.is_numeric()) {
                self.next();
            } else {
                break Tok::LitInt(i32::from_str(self.slice()).map_err(|e| {
                    Spanned::new(LexError::InvalidLiteral(e.to_string()), self.span())
                })?);
            }
        })
    }

    fn lex_name(&mut self) -> Tok<'i> {
        fn ident<'i>(s: &'i str) -> Tok<'i> {
            if s.len() > 4 && &s[0..4] == "Type" {
                if let Ok(i) = s[4..].parse() {
                    return Tok::Type(i);
                }
            }
            match &*s {
                "fun" => Tok::Fun,
                "struct" => Tok::Struct,
                "Type" => Tok::Type(0),
                "Int" => Tok::Int,
                "the" => Tok::The,
                "do" => Tok::Do,
                "move" => Tok::Move,
                "of" => Tok::Of,
                "type" => Tok::Data,
                _ => Tok::Name(s),
            }
        }

        loop {
            let c = self.peek();
            if c.map_or(false, |c| c.is_alphanumeric() || c == '_') {
                self.next();
            } else {
                break ident(self.slice());
            }
        }
    }

    /// Assumes that the next char exists
    fn next_tok(&mut self) -> LexResult<'i> {
        let tok = match self.peek().unwrap() {
            '(' => {
                self.next();
                Tok::POpen
            }
            ')' => {
                self.next();
                Tok::PClose
            }
            '{' => {
                self.next();
                Tok::BraceOpen
            }
            '}' => {
                self.next();
                Tok::BraceClose
            }
            ';' => {
                self.next();
                Tok::Semi
            }
            ',' => {
                self.next();
                Tok::Comma
            }
            '.' => {
                self.next();
                Tok::Dot
            }
            ':' => {
                self.next();
                Tok::Colon
            }
            '|' => {
                self.next();
                Tok::Bar
            }
            '+' => {
                self.next();
                Tok::Plus
            }
            '-' => {
                self.next();
                Tok::Minus
            }
            '*' => {
                self.next();
                Tok::Times
            }
            '/' => {
                self.next();
                Tok::Div
            }
            '=' => {
                self.next();
                if self.peek() == Some('>') {
                    self.next();
                    Tok::Arrow
                } else {
                    Tok::Equals
                }
            }
            '\r' => {
                self.next();
                if self.next() != Some('\n') {
                    return Err(Spanned::new(LexError::CarriageReturn, self.span()));
                } else {
                    self.was_newline = true;
                    Tok::Newline
                }
            }
            '\n' => {
                self.next();
                self.was_newline = true;
                Tok::Newline
            }
            c if c.is_numeric() => self.lex_number()?,
            c if c.is_alphabetic() || c == '_' => self.lex_name(),
            _ => return Err(Spanned::new(LexError::InvalidToken, self.span())),
        };
        Ok((self.last, tok, self.pos))
    }
}

impl<'i> std::iter::Iterator for Lexer<'i> {
    type Item = LexResult<'i>;

    fn next(&mut self) -> Option<LexResult<'i>> {
        // We need a newline token after each dedent so the parser knows to move on
        if self.was_dedent {
            self.was_dedent = false;
            return Some(Ok((self.last, Tok::Newline, self.pos)));
        }

        self.last = self.pos;

        if self.was_newline {
            match self.handle_indent() {
                Some(Ok(r)) => return Some(Ok((self.last, r, self.pos))),
                Some(Err(e)) => return Some(Err(Spanned::new(e, Span(self.last, self.pos)))),
                None => (),
            }
        }

        self.consume_whitespace();
        self.last = self.pos;

        if self.peek().is_none() {
            return None;
        } else {
            let tok = self.next_tok();
            // Suppress a newline before an indent token, to make the grammar simpler
            if tok.as_ref().map_or(false, |x| x.1 == Tok::Newline) {
                let p = self.save();
                let z = self.indent.clone();
                match self.handle_indent() {
                    Some(Ok(Tok::Indent)) => return Some(Ok((self.last, Tok::Indent, self.pos))),
                    Some(Err(e)) => return Some(Err(Spanned::new(e, Span(self.last, self.pos)))),
                    _ => {
                        // It wasn't an indent or tab error, so reset to before we called handle_indent() and emit the newline
                        self.was_dedent = false;
                        self.was_newline = true;
                        self.load(p);
                        self.indent = z;
                    }
                }
            }
            Some(tok)
        }
    }
}

impl LexError {
    pub fn to_string(&self) -> String {
        match self {
            LexError::Tabs => "Found tab character, please use spaces for indentation".to_string(),
            LexError::InvalidToken => "Invalid token".to_string(),
            LexError::InvalidLiteral(e) => format!("Invalid literal: {}", e),
            LexError::CarriageReturn => {
                "Expected newline '\\n' after carriage return '\\r'".to_string()
            }
            LexError::Other(s) => s.clone(),
        }
    }
}

impl<'i> fmt::Display for Tok<'i> {
    /// For displaying errors ("unexpected {}, expected {}")
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Tok::*;
        match self {
            Fun => write!(f, "'fun'"),
            Int => write!(f, "'Int'"),
            Type(0) => write!(f, "'Type'"),
            Type(i) => write!(f, "'Type{}'", i),
            Struct => write!(f, "'struct'"),
            The => write!(f, "'the'"),
            Do => write!(f, "'do'"),
            Move => write!(f, "'move'"),
            Of => write!(f, "'of'"),
            Data => write!(f, "'type'"),

            Dot => write!(f, "'.'"),
            Comma => write!(f, "','"),
            Semi => write!(f, "';'"),
            POpen => write!(f, "'('"),
            PClose => write!(f, "')'"),
            BraceOpen => write!(f, "'{{'"),
            BraceClose => write!(f, "'}}'"),
            Colon => write!(f, "':'"),
            Bar => write!(f, "'|'"),
            Plus => write!(f, "'+'"),
            Minus => write!(f, "'-'"),
            Times => write!(f, "'*'"),
            Div => write!(f, "'/'"),
            Arrow => write!(f, "'=>'"),
            Equals => write!(f, "'='"),

            Newline => write!(f, "newline"),
            LitInt(_) => write!(f, "int literal"),
            Name(_) => write!(f, "identifier"),
            Indent => write!(f, "indent"),
            Dedent => write!(f, "dedent"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_indent() {
        let lex = Lexer::new(
            r#"a
    : Int
    = 3
"#,
        );
        let v: Vec<Tok> = lex.map(|x| x.unwrap().1).collect();
        use Tok::*;
        assert_eq!(
            &v,
            &[
                Name("a"),
                Indent,
                Colon,
                Int,
                Newline,
                Equals,
                LitInt(3),
                Newline,
                Dedent,
                Newline,
            ]
        );
    }
}
