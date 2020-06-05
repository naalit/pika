//! Whitespace-sensitive lexer
//! We enforce spaces instead of tabs

use crate::error::{Span, Spanned};
use std::fmt;
use std::str::FromStr;

pub type LexResult<'i> = Result<(usize, Tok<'i>, usize), Spanned<LexError>>;

#[derive(Clone, Debug)]
pub enum LexError {
    Tabs,
    InvalidToken,
    InvalidLiteral,
    CarriageReturn,
    Other(String),
}

#[derive(Clone, Debug)]
pub enum Tok<'i> {
    Fun,           // "fun"
    Type,          // "Type"
    Int,           // "Int"
    Struct,        // "struct"
    Do,            // "do"
    The,           // "the"
    Tag,           // "tag"
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

    fn handle_indent(&mut self) -> Option<Tok<'i>> {
        for i in self.indent.clone() {
            for _ in 0..i {
                if self.peek() != Some(' ') {
                    // If the line is blank, we don't care. Skip it and do the next one.
                    if self.peek() == Some('\n') {
                        self.next();
                        return self.handle_indent();
                    } else if self.peek() == Some('\r') {
                        self.next();
                        if self.next() != Some('\n') {
                            todo!("give an error");
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
                    return Some(Tok::Dedent);
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
            return Some(Tok::Indent);
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
                break Tok::LitInt(
                    i32::from_str(self.slice())
                        .map_err(|_| Spanned::new(LexError::InvalidLiteral, self.span()))?,
                );
            }
        })
    }

    fn lex_name(&mut self) -> Tok<'i> {
        fn ident<'i>(s: &'i str) -> Tok<'i> {
            match &*s {
                "fun" => Tok::Fun,
                "struct" => Tok::Struct,
                "Type" => Tok::Type,
                "Int" => Tok::Int,
                "the" => Tok::The,
                "do" => Tok::Do,
                "tag" => Tok::Tag,
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
            if let Some(r) = self.handle_indent() {
                return Some(Ok((self.last, r, self.pos)));
            }
        }

        self.consume_whitespace();
        self.last = self.pos;

        if self.peek().is_none() {
            return None;
        } else {
            Some(self.next_tok())
        }
    }
}

impl LexError {
    pub fn to_string(&self) -> String {
        match self {
            LexError::Tabs => "Found tab character, please use spaces".to_string(),
            LexError::InvalidToken => "Invalid token".to_string(),
            LexError::InvalidLiteral => "Invalid literal".to_string(),
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
            Type => write!(f, "'Type'"),
            Struct => write!(f, "'struct'"),
            The => write!(f, "'the'"),
            Do => write!(f, "'do'"),
            Tag => write!(f, "'tag'"),

            Dot => write!(f, "'.'"),
            Comma => write!(f, "','"),
            Semi => write!(f, "';'"),
            POpen => write!(f, "'('"),
            PClose => write!(f, "')'"),
            BraceOpen => write!(f, "'{{'"),
            BraceClose => write!(f, "'}}'"),
            Colon => write!(f, "':'"),
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
