//! Significant indentation overview:
//! There are three tokens we can emit when we see a line break: INDENT, DEDENT, and NEWLINE.
//! If the next non-empty line is indented more than the previous, we emit an INDENT token (and no NEWLINE).
//! If it's the same indentation, we emit one NEWLINE token. We don't emit NEWLINEs for black lines, but we do for semicolons.
//!   (so a semicolon is like a line break + the same indentation as the current line.)
//! If it's a lower indentation level, we emit the appropriate number of DEDENTs and then a NEWLINE.

use crate::common::*;
// use crate::error::{Span, Spanned};
use ropey::RopeSlice;
use std::collections::VecDeque;
use std::fmt;
use std::iter::Peekable;
use std::str::FromStr;

use super::*;

pub type STok = Spanned<Tok>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidToken(char),
    InvalidLiteral(String),
    InvalidEscape(char),
    UnclosedString,
    /// This is used for specific errors that occur in one place, in the parser or lexer.
    Other(String),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Literal {
    Positive(u64),
    /// This should always be negative.
    Negative(i64),
    Float(u64),
    String(Name),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Tok {
    // Keywords
    Fun,
    Let,
    Impl,
    Do,
    Struct,
    Sig,
    /// This is lowercase `type`
    Type,
    Case,
    Of,
    /// This is uppercase `Type`. TODO make it a builtin instead of a keyword?
    TypeType,
    With,
    Pure,
    Where,
    Raise,
    Catch,
    And,
    Or,
    If,
    Then,
    Else,
    Eff,
    Box,
    Unbox,

    // Symbols the lexer recognizes as a "binary operator"
    Colon,     // :
    Equals,    // =
    Arrow,     // ->
    WideArrow, // =>
    Plus,      // +
    Minus,     // -
    Times,     // *
    Div,       // /
    Bar,       // |
    Dot,       // .
    Comma,     // ,
    Exp,       // **
    Mod,       // %
    Xor,       // ^^
    LShift,    // <<
    RShift,    // >>
    BitAnd,    // &
    Gt,        // >
    GtE,       // >=
    Lt,        // <
    LtE,       // <=
    Eq,        // ==
    NEq,       // !=
    LPipe,     // <|
    RPipe,     // |>

    // Tokens with a payload
    Lit(Literal),
    Name(Name),
    String(String),

    // Other tokens
    Indent,
    Dedent,
    At,      // @
    POpen,   // (
    PClose,  // )
    SOpen,   // [
    SClose,  // ]
    COpen,   // {
    CClose,  // }
    Newline, // \n or ;
    /// Backslash is reserved but not used for anything right now
    /// It may eventually be used as a line continuation character, at the start of the line like wisp's '.'
    Backslash, // \

    Error(LexError),
}

pub struct Lexer<'i> {
    chars: Peekable<ropey::iter::Chars<'i>>,
    input: RopeSlice<'i>,
    db: &'i dyn Parser,
    tok_start: usize,
    pos: usize,

    indent_stack: Vec<usize>,
    pending_toks: VecDeque<STok>,
}

impl<'i> Lexer<'i> {
    pub fn new(db: &'i dyn Parser, input: RopeSlice<'i>) -> Self {
        Lexer {
            db,
            chars: input.chars().peekable(),
            input,
            tok_start: 0,
            pos: 0,
            indent_stack: Vec::new(),
            pending_toks: VecDeque::new(),
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().cloned()
    }

    fn next(&mut self) -> Option<char> {
        self.pos += self.peek()?.len_utf8();
        self.chars.next()
    }

    pub fn span(&self) -> RelSpan {
        self.tok_start..self.pos
    }
    fn slice(&self) -> RopeSlice<'i> {
        self.input.slice(self.tok_start..self.pos)
    }

    fn skip_whitespace(&mut self) {
        while let Some(next) = self.peek() {
            // Skip line comments, but don't consume the newline
            if next == '#' {
                while self.peek().map_or(false, |x| x != '\n') {
                    self.next();
                }
            } else if next.is_whitespace() && next != '\n' {
                self.next();
            } else {
                break;
            }
        }
    }

    fn tok(&mut self, tok: Tok) -> STok {
        self.next();
        (tok, self.span())
    }

    fn tok_in_place(&self, tok: Tok) -> STok {
        (tok, self.span())
    }

    fn lex_number(&mut self) -> STok {
        let mut buf = String::new();
        let neg = self.peek() == Some('-');
        if neg {
            buf.push(self.next().unwrap());
        }
        let mut base = 10;
        if self.peek() == Some('0') {
            buf.push(self.next().unwrap());
            match self.peek() {
                Some('x') => {
                    self.next();
                    base = 16;
                }
                Some('b') => {
                    self.next();
                    base = 2;
                }
                _ => (),
            }
        }
        let mut float = false;
        while let Some(next) = self.peek() {
            if next.is_digit(base) {
                buf.push(next);
                self.next();
            } else if next == '_' {
                self.next();
            } else if next.is_alphanumeric() {
                self.next();
                return (
                    Tok::Error(LexError::InvalidLiteral(format!(
                        "Invalid digit for int literal: {}",
                        next
                    ))),
                    self.pos - 1..self.pos,
                );
            } else if next == '.' {
                float = true;
                buf.push(next);
                self.next();
            } else {
                break;
            }
        }
        self.tok_in_place(if float {
            match f64::from_str(&buf) {
                Ok(f) => Tok::Lit(Literal::Float(f.to_bits())),
                Err(e) => Tok::Error(LexError::InvalidLiteral(e.to_string())),
            }
        } else if neg {
            match i64::from_str_radix(&buf, base) {
                Ok(n) => Tok::Lit(Literal::Negative(n)),
                // TODO when `ParseIntError::kind()` gets stabilized (or Pika switches to nightly Rust) make custom error messages
                Err(e) => Tok::Error(LexError::InvalidLiteral(e.to_string())),
            }
        } else {
            match u64::from_str_radix(&buf, base) {
                Ok(n) => Tok::Lit(Literal::Positive(n)),
                Err(e) => Tok::Error(LexError::InvalidLiteral(e.to_string())),
            }
        })
    }

    fn lex_name(&mut self) -> STok {
        while let Some(next) = self.peek() {
            if next.is_alphanumeric() || next == '_' {
                self.next();
            } else {
                break;
            }
        }
        let tok = match &*self.slice().to_string() {
            "fun" => Tok::Fun,
            "let" => Tok::Let,
            "impl" => Tok::Impl,
            "type" => Tok::Type,
            "Type" => Tok::TypeType,
            "case" => Tok::Case,
            "with" => Tok::With,
            "pure" => Tok::Pure,
            "raise" => Tok::Raise,
            "catch" => Tok::Catch,
            "and" => Tok::And,
            "or" => Tok::Or,
            "if" => Tok::If,
            "then" => Tok::Then,
            "else" => Tok::Else,
            "box" => Tok::Box,
            "unbox" => Tok::Unbox,
            // Where technically ends one block and starts another one, but we ignore that.
            "where" => Tok::Where,
            "eff" => Tok::Eff,
            "do" => Tok::Do,
            "struct" => Tok::Struct,
            "sig" => Tok::Sig,
            "of" => Tok::Of,
            s => Tok::Name(self.db.name(s.to_string())),
        };
        self.tok_in_place(tok)
    }

    fn try_lex_binop(&mut self) -> Option<STok> {
        match self.peek()? {
            ':' => Some(self.tok(Tok::Colon)),
            '.' => Some(self.tok(Tok::Dot)),
            ',' => Some(self.tok(Tok::Comma)),
            '|' => {
                self.next();
                if self.peek() == Some('>') {
                    Some(self.tok(Tok::RPipe))
                } else {
                    Some(self.tok_in_place(Tok::Bar))
                }
            }

            '+' => Some(self.tok(Tok::Plus)),
            '*' => {
                self.next();
                if self.peek() == Some('*') {
                    Some(self.tok(Tok::Exp))
                } else {
                    Some(self.tok_in_place(Tok::Times))
                }
            }
            '/' => Some(self.tok(Tok::Div)),
            '%' => Some(self.tok(Tok::Mod)),

            '^' => {
                self.next();
                if self.peek() == Some('^') {
                    Some(self.tok(Tok::Xor))
                } else {
                    Some(self.tok_in_place(Tok::Error(LexError::Other("Ambiguous operator '^': use '**' for exponentiation, and '^^' for bitwise xor".into()))))
                }
            }
            '<' => {
                self.next();
                Some(match self.peek() {
                    Some('<') => self.tok(Tok::LShift),
                    Some('=') => self.tok(Tok::LtE),
                    Some('|') => self.tok(Tok::RPipe),
                    _ => self.tok_in_place(Tok::Lt),
                })
            }
            '>' => {
                self.next();
                Some(match self.peek() {
                    Some('>') => self.tok(Tok::RShift),
                    Some('=') => self.tok(Tok::GtE),
                    _ => self.tok_in_place(Tok::Gt),
                })
            }
            '&' => {
                self.next();
                if self.peek() == Some('&') {
                    Some(self.tok_in_place(Tok::Error(LexError::Other(
                        "Invalid operator '&&': use 'and' for logical and".into(),
                    ))))
                } else {
                    Some(self.tok_in_place(Tok::BitAnd))
                }
            }

            '!' => {
                self.next();
                if self.peek() == Some('=') {
                    Some(self.tok(Tok::NEq))
                } else {
                    None
                }
            }
            '=' => {
                self.next();
                Some(match self.peek() {
                    Some('>') => self.tok(Tok::WideArrow),
                    Some('=') => self.tok(Tok::Eq),
                    _ => self.tok_in_place(Tok::Equals),
                })
            }
            // '-' could be the start of a negative number
            // This seems to be the best way to access the next character
            '-' if self
                .input
                .slice(self.pos + 1..)
                .chars()
                .next()
                .map_or(true, |x| !x.is_numeric()) =>
            {
                self.next();
                if self.peek() == Some('>') {
                    Some(self.tok(Tok::Arrow))
                } else {
                    Some(self.tok_in_place(Tok::Minus))
                }
            }
            _ => None,
        }
    }

    fn lex_other(&mut self) -> STok {
        match self.peek().unwrap() {
            '(' => self.tok(Tok::POpen),
            ')' => self.tok(Tok::PClose),
            '[' => self.tok(Tok::SOpen),
            ']' => self.tok(Tok::SClose),
            '{' => self.tok(Tok::COpen),
            '}' => self.tok(Tok::CClose),

            '@' => self.tok(Tok::At),
            '\\' => self.tok(Tok::Backslash),
            ';' => self.tok(Tok::Newline),

            '\n' => {
                // We're going to emit one or more tokens which might include newline, indent, and dedent
                // First find the next non-empty line and record its starting position
                let mut start_pos = 0;
                while let Some(c) = self.peek() {
                    match c {
                        '\n' => start_pos = 0,
                        ' ' => start_pos += 1,
                        x if x.is_whitespace() => {
                            return self.tok(Tok::Error(LexError::Other(
                                "Only spaces are supported for indentation".to_string(),
                            )))
                        }
                        '#' => {
                            self.skip_whitespace();
                            continue;
                        }
                        _ => break,
                    }
                    self.next();
                }
                let mut i = 0;
                while i < self.indent_stack.len() {
                    if start_pos >= self.indent_stack[i] {
                        start_pos -= self.indent_stack[i];
                        i += 1;
                    } else if start_pos == 0 {
                        self.pending_toks.push_back(self.tok_in_place(Tok::Dedent));
                        self.indent_stack.remove(i);
                    } else {
                        return self.tok_in_place(Tok::Error(LexError::Other(
                            "Inconsistent indentation: dedent doesn't match any previous indentation level".to_string(),
                        )));
                    }
                }
                if start_pos > 0 {
                    self.indent_stack.push(start_pos);
                    self.pending_toks.push_back(self.tok_in_place(Tok::Indent));
                } else {
                    self.pending_toks.push_back(self.tok_in_place(Tok::Newline));
                }

                self.pending_toks.pop_front().unwrap()
            }

            '"' => {
                self.next();
                let mut buf = String::new();
                loop {
                    match self.next() {
                        Some('"') => break self.tok_in_place(Tok::String(buf)),
                        Some('\\') => {
                            // Escape
                            match self.next() {
                                Some('\\') => {
                                    buf.push('\\');
                                }
                                Some('n') => {
                                    buf.push('\n');
                                }
                                Some('t') => {
                                    buf.push('\t');
                                }
                                Some(c) => {
                                    let r = (
                                        Tok::Error(LexError::InvalidEscape(c)),
                                        self.pos - 2..self.pos,
                                    );
                                    // Try to find the terminating " to avoid further errors
                                    while self.next().map_or(false, |x| x != '"') {}
                                    break r;
                                }
                                None => {
                                    break self.tok_in_place(Tok::Error(LexError::UnclosedString))
                                }
                            }
                        }
                        Some(c) => buf.push(c),
                        None => break self.tok_in_place(Tok::Error(LexError::UnclosedString)),
                    }
                }
            }

            // This is called after `try_lex_binop()`, so if we get a '-' it must be a number
            x if x.is_numeric() || x == '-' => self.lex_number(),
            x if x.is_alphabetic() || x == '_' => self.lex_name(),
            x => self.tok(Tok::Error(LexError::InvalidToken(x))),
        }
    }
}

impl<'i> Iterator for Lexer<'i> {
    type Item = STok;

    fn next(&mut self) -> Option<STok> {
        if let Some(tok) = self.pending_toks.pop_front() {
            return Some(tok);
        }

        self.skip_whitespace();

        // This is where the actual token starts
        self.tok_start = self.pos;

        if let Some(binop) = self.try_lex_binop() {
            return Some(binop);
        }

        if self.peek().is_some() {
            let other = self.lex_other();
            Some(other)
        } else {
            for _ in 0..self.indent_stack.len() {
                self.pending_toks.push_back(self.tok_in_place(Tok::Dedent));
            }
            self.indent_stack.clear();
            self.pending_toks.pop_front()
        }
    }
}

pub fn lexerror_to_error(lex: LexError, span: RelSpan) -> Error {
    let mut gen = ariadne::ColorGenerator::default();
    let a = gen.next();
    let b = gen.next();
    let message = match lex {
        LexError::InvalidToken(c) => Doc::start("Invalid token: '").add(c, b).add("'", ()),
        LexError::InvalidLiteral(e) => Doc::start("Invalid literal: '").add(e, b).add("'", ()),
        LexError::InvalidEscape(e) => Doc::start("Invalid escape sequence: '")
            .add('\\', b)
            .add(e, b)
            .add("'", ()),
        LexError::UnclosedString => Doc::start("Unclosed ")
            .add("string literal:", a)
            .add(" expected a terminator '", ())
            .add('"', b)
            .add("' here", ()),
        LexError::Other(s) => Doc::start(s),
    };
    Error {
        severity: Severity::Error,
        message: message.clone(),
        primary: Label {
            span,
            message,
            color: Some(b),
        },
        secondary: Vec::new(),
        note: None,
    }
}

impl<'i> fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Tok::Fun => "'fun'",
            Tok::Let => "'val'",
            Tok::Impl => "'impl'",
            Tok::Do => "'do'",
            Tok::Struct => "'struct'",
            Tok::Sig => "'sig'",
            Tok::Type => "'type'",
            Tok::Case => "'case'",
            Tok::Of => "'of'",
            Tok::TypeType => "'Type'",
            Tok::With => "'with'",
            Tok::Pure => "'pure'",
            Tok::Where => "'where'",
            Tok::Raise => "'raise'",
            Tok::Catch => "'catch'",
            Tok::And => "'and'",
            Tok::Or => "'or'",
            Tok::If => "'if'",
            Tok::Then => "'then'",
            Tok::Else => "'else'",
            Tok::Eff => "'eff'",
            Tok::Box => "'box'",
            Tok::Unbox => "'unbox'",
            Tok::Colon => "':'",
            Tok::Equals => "'='",
            Tok::Arrow => "'->'",
            Tok::WideArrow => "'=>'",
            Tok::Plus => "'+'",
            Tok::Minus => "'-'",
            Tok::Times => "'*'",
            Tok::Div => "'/'",
            Tok::Mod => "'%'",
            Tok::Bar => "'|'",
            Tok::Dot => "'.'",
            Tok::Comma => "','",
            Tok::Exp => "'**'",
            Tok::Xor => "'^^'",
            Tok::LShift => "'<<'",
            Tok::RShift => "'>>'",
            Tok::BitAnd => "'&'",
            Tok::Gt => "'>'",
            Tok::GtE => "'>='",
            Tok::Lt => "'<'",
            Tok::LtE => "'<='",
            Tok::Eq => "'=='",
            Tok::NEq => "'!='",
            Tok::LPipe => "'<|'",
            Tok::RPipe => "'|>'",
            Tok::Lit(_) => "literal",
            Tok::Name(_) => "name",
            Tok::String(_) => "string literal",
            Tok::At => "'@'",
            Tok::POpen => "'('",
            Tok::PClose => "')'",
            Tok::SOpen => "'['",
            Tok::SClose => "']'",
            Tok::COpen => "'{'",
            Tok::CClose => "'}'",
            Tok::Indent => "indent",
            Tok::Dedent => "dedent",
            Tok::Newline => "newline",
            Tok::Backslash => "'\\'",
            Tok::Error(_) => "<error>",
        })
    }
}
