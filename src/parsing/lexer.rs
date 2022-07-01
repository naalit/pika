//! Significant indentation overview:
//! There are three tokens we can emit when we see a line break: INDENT, DEDENT, and NEWLINE.
//! If the next non-empty line is indented more than the previous, we emit an INDENT token (and no NEWLINE).
//! If it's the same indentation, we emit one NEWLINE token. We don't emit NEWLINEs for blank lines, but we do for semicolons.
//!   (so a semicolon is like a line break + the same indentation as the current line.)
//! If it's a lower indentation level, we emit the appropriate number of DEDENTs and then a NEWLINE.

use crate::common::*;
// use crate::error::{Span, Spanned};
use ropey::RopeSlice;
use std::collections::VecDeque;
use std::fmt;
use std::iter::Peekable;

use super::*;

pub type Tok = SyntaxKind;
type STok = (SyntaxKind, u32);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexResult {
    pub kind: Vec<SyntaxKind>,
    pub start: Vec<u32>,
    pub error: Vec<Spanned<LexError>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LexError {
    InvalidToken(char),
    InvalidLiteral(String),
    InvalidEscape(char),
    UnclosedString,
    /// This is used for specific errors that occur in one place, in the parser or lexer.
    Other(String),
}

pub struct Lexer<'i> {
    chars: Peekable<ropey::iter::Chars<'i>>,
    input: RopeSlice<'i>,
    tok_start: u32,
    pos: u32,

    indent_stack: Vec<usize>,
    pending_toks: VecDeque<STok>,
    errors: Vec<Spanned<LexError>>,
}

impl<'i> Lexer<'i> {
    pub fn new(input: RopeSlice<'i>) -> Self {
        Lexer {
            chars: input.chars().peekable(),
            input,
            tok_start: 0,
            pos: 0,
            indent_stack: Vec::new(),
            pending_toks: VecDeque::new(),
            errors: Vec::new(),
        }
    }

    fn peek(&mut self) -> Option<char> {
        self.chars.peek().cloned()
    }

    fn next(&mut self) -> Option<char> {
        self.pos += 1;
        self.chars.next()
    }

    pub fn span(&self) -> RelSpan {
        RelSpan::new(self.tok_start, self.pos)
    }
    fn slice(&self) -> RopeSlice<'i> {
        self.input.slice(self.tok_start as usize..self.pos as usize)
    }

    fn process_trivia(&mut self) {
        #[derive(PartialEq)]
        enum Mode {
            None,
            Comment,
            Space,
        }
        let mut mode = Mode::None;
        while let Some(next) = self.peek() {
            // Process line comments, but don't consume the newline
            if next == '#' {
                if mode == Mode::Space {
                    self.pending_toks.push_back(self.tok_in_place(Tok::Comment));
                    self.tok_start = self.pos;
                }
                mode = Mode::Comment;
                while self.peek().map_or(false, |x| x != '\n') {
                    self.next();
                }
            } else if next.is_whitespace() && next != '\n' {
                if mode == Mode::Comment {
                    self.pending_toks
                        .push_back(self.tok_in_place(Tok::Whitespace));
                    self.tok_start = self.pos;
                }
                mode = Mode::Space;
                self.next();
            } else {
                if mode != Mode::None {
                    self.pending_toks
                        .push_back(self.tok_in_place(Tok::Whitespace));
                    self.tok_start = self.pos;
                }
                break;
            }
        }
    }

    fn tok(&mut self, tok: Tok) -> STok {
        self.next();
        (tok, self.tok_start)
    }

    fn tok_in_place(&self, tok: Tok) -> STok {
        (tok, self.tok_start)
    }

    fn lex_number(&mut self) -> STok {
        // No error checking, that all happens in the typechecker
        // So this is just a regex `-?[A-Za-z0-9_]*(.[A-Za-z0-9_]*)?`
        // and it's only called when the input starts with `-?[0-9]`
        if self.peek() == Some('-') {
            self.next();
        }
        while self
            .peek()
            .map_or(false, |x| x.is_alphanumeric() || x == '_')
        {
            self.next();
        }
        if self.peek() == Some('.') {
            self.next();
            while self
                .peek()
                .map_or(false, |x| x.is_alphanumeric() || x == '_')
            {
                self.next();
            }
            return self.tok_in_place(Tok::FloatLit);
        } else {
            return self.tok_in_place(Tok::IntLit);
        }
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
            "fun" => Tok::FunKw,
            "let" => Tok::LetKw,
            "impl" => Tok::ImplKw,
            "type" => Tok::TypeKw,
            "Type" => Tok::TypeTypeKw,
            "case" => Tok::CaseKw,
            "with" => Tok::WithKw,
            "pure" => Tok::PureKw,
            "catch" => Tok::CatchKw,
            "and" => Tok::AndKw,
            "or" => Tok::OrKw,
            "if" => Tok::IfKw,
            "then" => Tok::ThenKw,
            "else" => Tok::ElseKw,
            "box" => Tok::BoxKw,
            "unbox" => Tok::UnboxKw,
            // Where technically ends one block and starts another one, but we ignore that.
            "where" => Tok::WhereKw,
            "eff" => Tok::EffKw,
            "do" => Tok::DoKw,
            "struct" => Tok::StructKw,
            "sig" => Tok::SigKw,
            "of" => Tok::OfKw,
            _ => Tok::Name,
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
                    self.errors.push((LexError::Other("Ambiguous operator '^': use '**' for exponentiation, and '^^' for bitwise xor".into()), self.span()));
                    Some(self.tok_in_place(Tok::Error))
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
                    self.errors.push((
                        LexError::Other("Invalid operator '&&': use 'and' for logical and".into()),
                        self.span(),
                    ));
                    Some(self.tok_in_place(Tok::Error))
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
                .slice(self.pos as usize + 1..)
                .chars()
                .next()
                .map_or(true, |x| !x.is_ascii_digit()) =>
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
                            self.next();
                            self.errors.push((
                                LexError::Other("Only spaces are supported for indentation".into()),
                                self.span(),
                            ));
                            return self.tok_in_place(Tok::Error);
                        }
                        '#' => {
                            self.process_trivia();
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
                        self.errors.push((LexError::Other("Inconsistent indentation: dedent doesn't match any previous indentation level".into()), self.span()));
                        return self.tok_in_place(Tok::Error);
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
                        Some('"') => break self.tok_in_place(Tok::StringLit),
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
                                    self.errors.push((
                                        LexError::InvalidEscape(c),
                                        RelSpan::new(self.pos - 2, self.pos),
                                    ));
                                    let r = (Tok::Error, self.tok_start);
                                    // Try to find the terminating " to avoid further errors
                                    while self.next().map_or(false, |x| x != '"') {}
                                    break r;
                                }
                                None => {
                                    self.errors.push((
                                        LexError::UnclosedString,
                                        RelSpan::new(self.tok_start, self.pos - 1),
                                    ));
                                    break self.tok_in_place(Tok::Error);
                                }
                            }
                        }
                        Some(c) => buf.push(c),
                        None => {
                            self.errors.push((
                                LexError::UnclosedString,
                                RelSpan::new(self.tok_start, self.pos - 1),
                            ));
                            break self.tok_in_place(Tok::Error);
                        }
                    }
                }
            }

            // This is called after `try_lex_binop()`, so if we get a '-' it must be a number
            x if x.is_numeric() || x == '-' => self.lex_number(),
            x if x.is_alphabetic() || x == '_' => self.lex_name(),
            x => {
                self.next();
                self.errors.push((LexError::InvalidToken(x), self.span()));
                self.tok_in_place(Tok::Error)
            }
        }
    }

    fn next_tok(&mut self) -> Option<STok> {
        if let Some(tok) = self.pending_toks.pop_front() {
            return Some(tok);
        }

        self.tok_start = self.pos;
        self.process_trivia();

        if let Some(tok) = self.pending_toks.pop_front() {
            return Some(tok);
        }

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

    pub fn lex(&mut self) -> LexResult {
        let mut kind = Vec::new();
        let mut start = Vec::new();
        while let Some((tok, pos)) = self.next_tok() {
            kind.push(tok);
            start.push(pos);
        }
        LexResult {
            kind,
            start,
            error: self.errors.split_off(0),
        }
    }
}

pub fn lexer_entry(db: &dyn Parser, file: File, id: SplitId) -> Option<LexResult> {
    let split = db.split(file, id)?;
    let mut lexer = Lexer::new(split.text.slice(..));
    Some(lexer.lex())
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
            .add("string literal", a)
            .add(": expected a terminator '", ())
            .add('"', b)
            .add("' here", ()),
        LexError::Other(s) => Doc::start(s),
    };
    Error {
        severity: Severity::Error,
        message: message.clone(),
        message_lsp: None,
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
            Tok::FunKw => "'fun'",
            Tok::LetKw => "'let'",
            Tok::ImplKw => "'impl'",
            Tok::DoKw => "'do'",
            Tok::StructKw => "'struct'",
            Tok::SigKw => "'sig'",
            Tok::TypeKw => "'type'",
            Tok::CaseKw => "'case'",
            Tok::OfKw => "'of'",
            Tok::TypeTypeKw => "'Type'",
            Tok::WithKw => "'with'",
            Tok::PureKw => "'pure'",
            Tok::WhereKw => "'where'",
            Tok::CatchKw => "'catch'",
            Tok::AndKw => "'and'",
            Tok::OrKw => "'or'",
            Tok::IfKw => "'if'",
            Tok::ThenKw => "'then'",
            Tok::ElseKw => "'else'",
            Tok::EffKw => "'eff'",
            Tok::BoxKw => "'box'",
            Tok::UnboxKw => "'unbox'",
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
            Tok::FloatLit => "float literal",
            Tok::IntLit => "float literal",
            Tok::Name => "name",
            Tok::StringLit => "string literal",
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
            Tok::Error => "<error>",

            Tok::Whitespace => "whitespace",
            Tok::Comment => "comment",

            Tok::Eof => "end of file",

            // composite kinds that shouldn't be produced by the lexer
            _ => "<??>",
        })
    }
}
