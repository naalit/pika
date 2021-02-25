//! Pika now uses a custom lexer, mostly to be more flexible about newlines.
//! Specifically, the lexer ignores newlines before or after a binary operator token, and inside parentheses (like Python).
//! Except, when there's a newline before an operator, it overrides the precedence so that the (last expression of the) last line is essentially inside parentheses.
//! Also, semicolons and newlines are 100% equivalent to the *parser*, so they use the same token, but the lexer never ignores semicolons like it does newlines.

use crate::common::*;
use crate::error::{Span, Spanned};
use std::collections::VecDeque;
use std::fmt;
use std::iter::Peekable;
use std::str::{Chars, FromStr};

/// The type lalrpop requires lexers emit
pub type LexResult<'i> = Result<(usize, Tok<'i>, usize), Spanned<LexError>>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidToken,
    InvalidLiteral(String),
    MissingTerminator(NestType),
    UnexpectedTerminator(NestType),
    /// This is used for specific errors that occur in one place, in the parser or lexer.
    Other(String),
}

impl ToError for Spanned<LexError> {
    fn to_error(self, file: FileId) -> Error {
        let s = format!("{}", *self);
        Error::new(file, format!("Parse error: {}", s), self.span(), s)
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum Literal {
    Positive(u64),
    /// This should always be negative.
    Negative(i64),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Tok<'i> {
    // Keywords
    Fun,
    Val,
    Impl,
    Do,
    Struct,
    Sig,
    /// This is lowercase `type`
    Type,
    Case,
    Of,
    End,
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
    Name(&'i str),

    // Other tokens
    Question,  // ?
    At,        // @
    POpen,     // (
    PClose,    // )
    SOpen,     // [
    SClose,    // ]
    COpen,     // {
    CClose,    // }
    Newline,   // \n or ;
    OpNewline, // "\n"+ before a binop
    Backslash, // \
}
impl<'i> Tok<'i> {
    /// Returns true if we should completely ignore newlines before this token.
    /// Currently only true for '=>', '->', '=' and ':'.
    fn is_special_binop(self) -> bool {
        match self {
            Tok::Equals | Tok::Colon | Tok::WideArrow | Tok::Arrow => true,
            _ => false,
        }
    }

    pub fn closes_type(self) -> Option<NestType> {
        match self {
            Tok::SClose => Some(NestType::Square),
            Tok::PClose => Some(NestType::Paren),
            Tok::CClose => Some(NestType::Curly),
            Tok::End => Some(NestType::Block),
            _ => None,
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum NestType {
    Paren,
    Square,
    Curly,
    /// Anything that ends with `end`
    Block,
}

pub struct Lexer<'i> {
    chars: Peekable<Chars<'i>>,
    input: &'i str,
    was_binop: bool,
    tok_start: usize,
    pos: usize,

    nesting: Vec<NestType>,

    /// We ignore newlines before binops, so as we find newlines we add their positions to pending_newlines but don't emit them.
    /// Then, if we hit a binop we clear pending_newlines and emit an OpNewline.
    /// If we hit something other than a newline or binop, we put in in pending_tok and emit all the newlines as Newline, then emit pending_tok.
    pending_newlines: VecDeque<usize>,
    pending_tok: Option<LexResult<'i>>,
}

impl<'i> Lexer<'i> {
    pub fn new(input: &'i str) -> Self {
        Lexer {
            chars: input.chars().peekable(),
            input,
            was_binop: false,
            tok_start: 0,
            pos: 0,
            nesting: Vec::new(),
            pending_newlines: VecDeque::new(),
            pending_tok: None,
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().cloned()
    }

    fn next(&mut self) -> Option<char> {
        self.pos += self.peek().unwrap().len_utf8();
        self.chars.next()
    }

    pub fn span(&self) -> Span {
        Span(self.tok_start, self.pos)
    }
    fn slice(&self) -> &'i str {
        &self.input[self.tok_start..self.pos]
    }

    fn skip_whitespace(&mut self) {
        while let Some(next) = self.peek() {
            // Skip line comments, but don't consume the newline
            if next == '#' {
                while self.peek().map_or(false, |x| x != '\n') {
                    self.next();
                }
            }
            // Ignore newlines immediately after binops or in parens
            else if next.is_whitespace()
                && (self.was_binop
                    || self.nesting.last().map_or(false, |x| *x == NestType::Paren)
                    || next != '\n')
            {
                self.next();
            } else {
                break;
            }
        }
    }

    fn tok(&mut self, tok: Tok<'i>) -> LexResult<'i> {
        self.next();
        Ok((self.tok_start, tok, self.pos))
    }

    fn tok_in_place(&self, tok: Tok<'i>) -> LexResult<'i> {
        Ok((self.tok_start, tok, self.pos))
    }

    fn nexpect(&mut self, t: NestType) -> Result<(), Spanned<LexError>> {
        let p = self.nesting.pop();
        match p {
            Some(p) if p == t => Ok(()),
            Some(p) => Err(Spanned::new(
                LexError::MissingTerminator(p),
                // Don't point at the current token, point at the spot where it's missing
                Span(self.tok_start, self.tok_start),
            )),
            None => Err(Spanned::new(LexError::UnexpectedTerminator(t), self.span())),
        }
    }

    fn lex_number(&mut self) -> LexResult<'i> {
        let neg = self.peek() == Some('-');
        if neg {
            self.next();
        }
        while let Some(next) = self.peek() {
            if next.is_numeric() {
                self.next();
            } else {
                break;
            }
        }
        self.tok_in_place(Tok::Lit(if neg {
            Literal::Negative(i64::from_str(self.slice()).map_err(|e| {
                // TODO when `ParseIntError::kind()` gets stabilized (or Pika switches to nightly Rust) make custom error messages
                Spanned::new(LexError::InvalidLiteral(e.to_string()), self.span())
            })?)
        } else {
            Literal::Positive(
                u64::from_str(self.slice()).map_err(|e| {
                    Spanned::new(LexError::InvalidLiteral(e.to_string()), self.span())
                })?,
            )
        }))
    }

    fn lex_name(&mut self) -> LexResult<'i> {
        while let Some(next) = self.peek() {
            if next.is_alphanumeric() || next == '_' {
                self.next();
            } else {
                break;
            }
        }
        let tok = match self.slice() {
            "fun" => Tok::Fun,
            "val" => Tok::Val,
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
            // Where technically ends one block and starts another one, but we ignore that.
            "where" => Tok::Where,
            "eff" => Tok::Eff,
            "do" => {
                self.nesting.push(NestType::Block);
                Tok::Do
            }
            "struct" => {
                self.nesting.push(NestType::Block);
                Tok::Struct
            }
            "sig" => {
                self.nesting.push(NestType::Block);
                Tok::Sig
            }
            "of" => {
                self.nesting.push(NestType::Block);
                Tok::Of
            }
            "end" => {
                self.nexpect(NestType::Block)?;
                Tok::End
            }
            s => Tok::Name(s),
        };
        self.tok_in_place(tok)
    }

    fn try_lex_binop(&mut self) -> Option<LexResult<'i>> {
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
                    Some(Err(Spanned::new(LexError::Other("ambiguous operator '^': use '**' for exponentiation, and '^^' for bitwise xor".into()), self.span())))
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
                    Some(Err(Spanned::new(
                        LexError::Other("invalid operator '&&': use 'and' for logical and".into()),
                        self.span(),
                    )))
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
            '-' if self.input[self.pos + 1..]
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

    fn lex_other(&mut self) -> LexResult<'i> {
        match self.peek().unwrap() {
            '(' => {
                self.nesting.push(NestType::Paren);
                self.tok(Tok::POpen)
            }
            ')' => {
                self.nexpect(NestType::Paren)?;
                self.tok(Tok::PClose)
            }
            '[' => {
                self.nesting.push(NestType::Square);
                self.tok(Tok::SOpen)
            }
            ']' => {
                self.nexpect(NestType::Square)?;
                self.tok(Tok::SClose)
            }
            '{' => {
                self.nesting.push(NestType::Curly);
                self.tok(Tok::COpen)
            }
            '}' => {
                self.nexpect(NestType::Curly)?;
                self.tok(Tok::CClose)
            }

            '?' => self.tok(Tok::Question),
            '@' => self.tok(Tok::At),
            '\\' => self.tok(Tok::Backslash),
            ';' => self.tok(Tok::Newline),

            // This is called after `try_lex_binop()`, so if we get a '-' it must be a number
            x if x.is_numeric() || x == '-' => self.lex_number(),
            x if x.is_alphabetic() || x == '_' => self.lex_name(),
            _ => Err(Spanned::new(LexError::InvalidToken, self.span())),
        }
    }
}

impl<'i> Iterator for Lexer<'i> {
    type Item = LexResult<'i>;

    fn next(&mut self) -> Option<LexResult<'i>> {
        // If we've already found a non-newline-or-binop, go through all the pending newlines, then emit the token
        if self.pending_tok.is_some() {
            if let Some(pos) = self.pending_newlines.pop_front() {
                // Newlines are one character, so the span is (pos - 1, pos)
                return Some(Ok((pos - 1, Tok::Newline, pos)));
            } else {
                return self.pending_tok.take();
            }
        }

        self.skip_whitespace();

        // Add any newlines to `pending_newlines`, don't emit them immediately
        while self.peek() == Some('\n') {
            self.next();
            self.pending_newlines.push_back(self.pos);
            self.skip_whitespace();
        }

        // This is where the actual token starts
        self.tok_start = self.pos;

        // If we hit a binop, emit a `OpNewline` if there's pending newlines, then emit the binop
        if let Some(binop) = self.try_lex_binop() {
            self.was_binop = true;
            // Ignore newlines for =>, ->, = and :, though, since precedence doesn't matter for them
            if self.pending_newlines.is_empty()
                || binop
                    .as_ref()
                    .map_or(false, |(_, t, _)| t.is_special_binop())
            {
                self.pending_newlines = VecDeque::new();
                return Some(binop);
            } else {
                let pos = self.pending_newlines.pop_back().unwrap();
                self.pending_newlines = VecDeque::new();
                self.pending_tok = Some(binop);
                return Some(Ok((pos - 1, Tok::OpNewline, pos)));
            }
        }

        if self.peek().is_some() {
            self.was_binop = false;
            let other = self.lex_other();
            if let Some(pos) = self.pending_newlines.pop_front() {
                self.pending_tok = Some(other);
                Some(Ok((pos - 1, Tok::Newline, pos)))
            } else {
                Some(other)
            }
        } else {
            None
        }
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LexError::InvalidToken => write!(f, "invalid token"),
            LexError::InvalidLiteral(e) => write!(f, "invalid literal: {}", e),
            LexError::MissingTerminator(t) => write!(
                f,
                "unclosed block: expected a terminator {} here",
                match t {
                    NestType::Block => "'end'",
                    NestType::Curly => "'}'",
                    NestType::Paren => "')'",
                    NestType::Square => "']'",
                }
            ),
            LexError::UnexpectedTerminator(t) => write!(
                f,
                "unexpected {} {}",
                match t {
                    NestType::Block => "'end'",
                    NestType::Curly => "closing '}'",
                    NestType::Paren => "closing ')'",
                    NestType::Square => "closing ']'",
                },
                match t {
                    NestType::Block => "outside of a block (like a `do` or `struct`)",
                    NestType::Curly => "without an opening '{'",
                    NestType::Paren => "without an opening '('",
                    NestType::Square => "without an opening '['",
                }
            ),
            LexError::Other(s) => write!(f, "{}", s),
        }
    }
}

impl<'i> fmt::Display for Tok<'i> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Tok::Fun => "'fun'",
            Tok::Val => "'val'",
            Tok::Impl => "'impl'",
            Tok::Do => "'do'",
            Tok::Struct => "'struct'",
            Tok::Sig => "'sig'",
            Tok::Type => "'type'",
            Tok::Case => "'case'",
            Tok::Of => "'of'",
            Tok::End => "'end'",
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
            Tok::Question => "'?'",
            Tok::At => "'@'",
            Tok::POpen => "'('",
            Tok::PClose => "')'",
            Tok::SOpen => "'['",
            Tok::SClose => "']'",
            Tok::COpen => "'{'",
            Tok::CClose => "'}'",
            Tok::Newline => "newline",
            Tok::OpNewline => "newline_",
            Tok::Backslash => "'\\'",
        })
    }
}
