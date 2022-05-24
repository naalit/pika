use std::cmp::Ordering;

use ropey::RopeSlice;
use rowan::{Checkpoint, GreenNode, GreenNodeBuilder};

use super::{lexer::*, SplitId};
use crate::common::*;

enum ParseError {
    Expected(Tok),
    ExpectedMsg(Cow<'static, str>),
    UnexpectedMsg(Cow<'static, str>),
    Other(Cow<'static, str>),
}
impl ParseError {
    fn to_error(self, span: RelSpan) -> Error {
        let mut gen = ariadne::ColorGenerator::default();
        let a = gen.next();
        let b = gen.next();
        let message = match self {
            ParseError::Expected(t) => Doc::start("expected ").add(t, a).space().add("here", ()),
            ParseError::ExpectedMsg(m) => Doc::start("expected ").add(m, a).space().add("here", ()),
            ParseError::UnexpectedMsg(m) => Doc::start("unexpected ").add(m, a),
            ParseError::Other(m) => Doc::start(m),
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
}

struct Parser<'a> {
    text: RopeSlice<'a>,
    builder: GreenNodeBuilder<'static>,
    lex_result: &'a LexResult,
    tok_idx: usize,
    errors: Vec<Spanned<ParseError>>,
}
impl<'a> Parser<'a> {
    // -- helper methods --

    fn skip_ws(&mut self) {
        while matches!(self.cur(), Tok::Whitespace | Tok::Comment) {
            self.advance_no_ws()
        }
    }

    /// Advances to the next non-trivia token, adding the current token to the current node that `builder` is on
    fn advance(&mut self) {
        self.advance_no_ws();
        self.skip_ws();
    }

    /// Like `advance`, but doesn't skip trivia
    fn advance_no_ws(&mut self) {
        let tok = self.lex_result.kind[self.tok_idx];
        let start = self.lex_result.start[self.tok_idx];
        let end = self.lex_result.start.get(self.tok_idx + 1).copied().unwrap_or_else(|| self.text.len_chars() as u32);
        let slice = self.text.slice(start as usize..end as usize);
        self.builder
            .token(tok.into(), &std::borrow::Cow::<'a, str>::from(slice));
        self.tok_idx += 1;
    }

    fn cur(&self) -> Tok {
        self.lex_result
            .kind
            .get(self.tok_idx)
            .copied()
            .unwrap_or(Tok::Eof)
    }

    fn tok_span(&self) -> RelSpan {
        let start = self.lex_result.start[self.tok_idx];
        let end = self.lex_result.start.get(self.tok_idx + 1).copied().unwrap_or_else(|| self.text.len_chars() as u32);
        start..end
    }

    fn expect(&mut self, t: Tok) {
        if self.cur() != t {
            self.errors.push((ParseError::Expected(t), self.tok_span()));
        } else {
            self.advance();
        }
    }

    fn maybe(&mut self, t: Tok) -> bool {
        if self.cur() == t {
            self.advance();
            true
        } else {
            false
        }
    }

    fn push(&mut self, t: Tok) {
        self.builder.start_node(t.into());
    }
    fn push_at(&mut self, cp: Checkpoint, t: Tok) {
        self.builder.start_node_at(cp, t.into());
    }
    fn checkpoint(&self) -> Checkpoint {
        self.builder.checkpoint()
    }
    fn pop(&mut self) {
        self.builder.finish_node();
    }

    fn var(&mut self) {
        self.push(Tok::Var);
        self.expect(Tok::Name);
        self.pop();
    }

    // -- definition parsing --

    fn defs(&mut self) {
        while !matches!(self.cur(), Tok::Eof | Tok::Dedent) {
            self.def();
        }
    }

    fn def_end(&mut self) {
        if matches!(self.cur(), Tok::Newline | Tok::Eof | Tok::Dedent) {
            if self.cur() == Tok::Newline {
                self.advance();
            }
        } else {
            let span = self.tok_span();
            self.errors.push((ParseError::ExpectedMsg("newline or end of definitions".into()), span));
        }
    }

    fn def(&mut self) {
        match self.cur() {
            Tok::FunKw => {
                self.push(Tok::FunDef);
                self.advance();

                self.var();

                self.push(Tok::Params);
                loop {
                    match self.cur() {
                        Tok::POpen | Tok::SOpen => _ = self.parse_group(),
                        t if t.starts_atom() => self.atom(),
                        // TODO better error handling heuristics here
                        // when should we give up on the function and when not?
                        _ => break,
                    }
                }
                self.pop();

                if self.maybe(Tok::Colon) {
                    self.push(Tok::Ty);
                    self.expr(());
                    self.pop();
                }
                // Allow function declarations without =
                if self.maybe(Tok::Equals) {
                    self.push(Tok::Body);
                    self.expr(());
                    self.pop();
                }

                self.pop();
                self.def_end();
            }
            Tok::TypeKw | Tok::EffKw => {
                let cp = self.checkpoint();
                self.advance();

                self.var();

                self.push(Tok::Params);
                loop {
                    match self.cur() {
                        Tok::POpen | Tok::SOpen => _ = self.parse_group(),
                        t if t.starts_atom() => self.atom(),
                        _ => break,
                    }
                }
                self.pop();

                if self.maybe(Tok::Equals) {
                    // Short form: type MyInt = i32 [where ...]
                    self.push_at(cp, Tok::TypeDefShort);

                    self.push(Tok::Ty);
                    self.expr(());
                    self.pop();
                } else {
                    self.push_at(cp, Tok::TypeDef);

                    self.expect(Tok::OfKw);
                    self.expect(Tok::Indent);

                    // constructors
                    loop {
                        self.push(Tok::ConsDef);

                        self.var();

                        self.push(Tok::Params);
                        loop {
                            match self.cur() {
                                Tok::POpen | Tok::SOpen => _ = self.parse_group(),
                                t if t.starts_atom() => self.atom(),
                                _ => break,
                            }
                        }
                        self.pop();

                        self.pop();

                        if !self.maybe(Tok::Newline) {
                            break;
                        }
                    }

                    self.expect(Tok::Dedent);
                }

                let mut had_newline = self.maybe(Tok::Newline);
                if self.maybe(Tok::WhereKw) {
                    had_newline = false;
                    self.push(Tok::BlockDef);

                    self.expect(Tok::Indent);
                    self.defs();
                    self.expect(Tok::Dedent);

                    self.pop();
                }

                self.pop();
                if !had_newline {
                    self.def_end();
                }
            }
            _ => {
                let span = self.tok_span();
                self.errors.push((ParseError::ExpectedMsg("definition".into()), span));
                self.advance();
            }
        }
    }

    // -- expression parsing --

    fn atom(&mut self) {
        match self.cur() {
            Tok::IntLit => {
                self.push(Tok::Lit);
                self.advance();
                self.pop();
            }
            Tok::POpen => {
                self.push(Tok::GroupedExpr);
                self.advance();
                if !self.maybe(Tok::PClose) {
                    self.expr(());
                    self.expect(Tok::PClose);    
                }
                self.pop();
            }
            Tok::Name => {
                self.var();
            }
            tok => {
                let span = self.tok_span();
                if tok.starts_atom() {
                    self.advance();
                }
                self.errors
                    .push((ParseError::ExpectedMsg("expression".into()), span));
            }
        }
    }

    fn resolve_app(&mut self, atoms: &mut Vec<Checkpoint>) {
        atoms.split_off(0).first().map(|&x| {
            self.push_at(x, Tok::AppList);
            self.pop();
        });
    }

    /// (start checkpoint, whether it must be a parameter)
    fn parse_group(&mut self) -> (Checkpoint, bool) {
        let (close, par, arg) = match self.cur() {
            Tok::SOpen => (Tok::SClose, Tok::ImpPar, Tok::ImpArg),
            Tok::POpen => (Tok::PClose, Tok::ExpPar, Tok::GroupedExpr),
            _ => unreachable!(),
        };
        let cp = self.checkpoint();
        self.advance();

        // `(: Type) -> ...` is allowed, usually used for traits `[x y z] [: Add x y z] -> x -> y -> z`
        if self.maybe(Tok::Colon) {
            self.push(Tok::Ty);
            self.expr(());
            self.pop();
            self.expect(close);
            self.push_at(cp, par);
            self.pop();
            return (cp, true);
        }
        // ()
        if self.maybe(close) {
            self.push_at(cp, arg);
            self.pop();
            return (cp, false);
        }

        self.expr(());
        if self.maybe(Tok::Colon) {
            self.push(Tok::Ty);
            self.expr(());
            self.pop();
            self.expect(close);
            self.push_at(cp, par);
            self.pop();
            (cp, true)
        } else {
            self.expect(close);
            self.push_at(cp, arg);
            self.pop();
            (cp, false)
        }
    }

    fn maybe_with(&mut self) {
        if self.maybe(Tok::WithKw) {
            self.push(Tok::WithClause);
            self.advance();

            self.expr(Prec::Bitwise);

            while self.maybe(Tok::Comma) {
                self.expr(Prec::Bitwise);
            }

            self.pop();
        }
    }

    fn lambda_pi(&mut self, lhs: Checkpoint) {
        match self.cur() {
            Tok::POpen | Tok::SOpen => _ = self.parse_group(),
            t if t.starts_atom() => self.atom(),
            Tok::WideArrow => {
                self.push_at(lhs, Tok::Params);
                self.pop();
                self.advance();

                // parse body
                self.push(Tok::Body);
                self.expr(());
                self.pop();

                self.push_at(lhs, Tok::Lam);
                self.pop();
            }
            Tok::Arrow => {
                self.push_at(lhs, Tok::Params);
                self.pop();
                self.advance();

                // parse body
                self.push(Tok::Body);
                self.expr(());
                self.pop();

                self.maybe_with();

                self.push_at(lhs, Tok::Pi);
                self.pop();
            }
            _ => {
                let span = self.tok_span();
                self.errors.push((
                    ParseError::ExpectedMsg("'=>' or '->' after parameter".into()),
                    span,
                ));
            }
        }
    }

    /// Parses an expression where all operators have at least the given precedence
    /// If `lhs` is `Some`, will only parse the operator and right hand side and add it to the provides lhs
    fn expr(&mut self, params: impl Into<ExprParams>) {
        let ExprParams {
            min_prec,
            lhs,
            allow_lambda,
        } = params.into();
        let mut atoms: Vec<Checkpoint> = lhs.iter().copied().collect();
        let lhs = match lhs {
            None => {
                let cp = self.checkpoint();
                match self.cur() {
                    // This case for indentation only appears after operators
                    Tok::Indent => {
                        self.push(Tok::GroupedExpr);
                        self.advance();
                        self.expr(());
                        self.expect(Tok::Dedent);
                        self.pop();
                    }
                    Tok::EffKw => {
                        self.push(Tok::EffPat);
                        self.advance();
                        self.atom();
                        self.atom();
                        self.pop();
                    }
                    Tok::CaseKw => {
                        self.push(Tok::Case);
                        self.advance();
                        // scrutinee
                        self.expr(());
                        self.expect(Tok::OfKw);
                        self.expect(Tok::Indent);

                        let mut made_error = false;
                        loop {
                            self.push(Tok::CaseBranch);

                            // Pattern
                            self.expr(ExprParams::no_lambda());
                            self.expect(Tok::WideArrow);

                            // Body
                            self.push(Tok::Body);
                            self.expr(());
                            self.pop();

                            self.pop();

                            match self.cur() {
                                Tok::Newline => self.advance(),
                                Tok::Dedent => {
                                    self.advance();
                                    break;
                                }
                                _ => {
                                    if !made_error {
                                        made_error = true;
                                        self.expect(Tok::Dedent);
                                    }
                                    self.advance();
                                }
                            }
                        }
                        self.pop();
                    }
                    // This should be able to handle
                    //
                    // if a
                    //   then b
                    //   else c
                    //
                    // because Tok::Min > Tok::If > everything else
                    // (so operator chaining is not allowed in an if condition if it starts on the `if` line)
                    Tok::IfKw => {
                        self.push(Tok::If);
                        self.advance();
                        // condition
                        self.expr(Prec::If);

                        // then branch
                        let indent = self.maybe(Tok::Indent);
                        self.expect(Tok::ThenKw);
                        self.expr(());

                        // else branch
                        if indent {
                            self.expect(Tok::Newline);
                        }
                        self.expect(Tok::ElseKw);
                        self.expr(());

                        if indent {
                            self.expect(Tok::Dedent);
                        }

                        self.pop();
                    }
                    _ => {
                        atoms.push(cp);
                        self.atom()
                    }
                }
                cp
            }
            Some(cp) => cp,
        };

        loop {
            match self.cur() {
                Tok::SOpen | Tok::POpen => {
                    let (cp, par) = self.parse_group();
                    if par {
                        self.lambda_pi(lhs);
                        return;
                    } else {
                        atoms.push(cp);
                    }
                }

                x if x.starts_atom() => {
                    atoms.push(self.checkpoint());
                    self.atom();
                }
                Tok::Dot => {
                    let cp = atoms.last().copied().unwrap_or_else(|| {
                        let span = self.tok_span();
                        self.errors.push((
                            ParseError::ExpectedMsg("expression before '.'".into()),
                            span,
                        ));
                        self.checkpoint()
                    });
                    self.push_at(cp, Tok::Member);
                    self.advance();
                    self.var();
                    self.pop();
                }
                // This indent appears before an operator (inc. application)
                // So implement operator chaining
                // If we're not at the outermost expression, though, pass control back there
                Tok::Indent => {
                    self.resolve_app(&mut atoms);
                    if min_prec == Prec::Min {
                        self.advance();
                        loop {
                            // Each line has an operator + rhs, then a newline
                            // This magically works for application as well!
                            self.expr((Prec::Min, Some(lhs)));
                            match self.cur() {
                                // don't allow more operators after dedent
                                Tok::Dedent => {
                                    self.advance();
                                    return;
                                }
                                Tok::Newline => {
                                    self.advance();
                                    continue;
                                }
                                _ => {
                                    let span = self.tok_span();
                                    self.errors.push((ParseError::Expected(Tok::Dedent), span));
                                    break;
                                }
                            }
                        }
                    } else {
                        break;
                    }
                }
                // Lambda time
                Tok::WideArrow if allow_lambda => {
                    self.lambda_pi(lhs);
                    return;
                }
                // >= makes it right associative
                Tok::Arrow => {
                    self.resolve_app(&mut atoms);
                    if Prec::Arrow >= min_prec {
                        self.push_at(lhs, Tok::Arrow.into());
                        self.advance();
                        self.expr(Prec::Arrow);
                        self.pop();
                    } else {
                        break;
                    }
                }
                op if op.binop_prec().is_some() => {
                    self.resolve_app(&mut atoms);

                    let prec = op.binop_prec().unwrap();
                    if prec > min_prec {
                        self.push(Tok::BinOpKind.into());
                        self.advance_no_ws();
                        self.pop();

                        self.push_at(lhs, Tok::BinOp.into());
                        self.skip_ws();
                        self.expr(prec);
                        self.pop();
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }

        self.resolve_app(&mut atoms);
    }
}

struct ExprParams {
    min_prec: Prec,
    lhs: Option<Checkpoint>,
    allow_lambda: bool,
}
impl ExprParams {
    fn new() -> Self {
        ().into()
    }
    fn no_lambda() -> Self {
        ExprParams {
            allow_lambda: false,
            ..Self::new()
        }
    }
}
impl From<()> for ExprParams {
    fn from(_: ()) -> Self {
        ExprParams {
            min_prec: Prec::Min,
            lhs: None,
            allow_lambda: true,
        }
    }
}
impl From<Prec> for ExprParams {
    fn from(min_prec: Prec) -> Self {
        ExprParams {
            min_prec,
            lhs: None,
            allow_lambda: true,
        }
    }
}
impl From<(Prec, Option<Checkpoint>)> for ExprParams {
    fn from((min_prec, lhs): (Prec, Option<Checkpoint>)) -> Self {
        ExprParams {
            min_prec,
            lhs,
            allow_lambda: true,
        }
    }
}

pub struct ParseResult {
    pub errors: Vec<Error>,
    pub green: GreenNode,
}

pub fn parser_entry(db: &dyn super::Parser, file: File, split: SplitId) -> Option<ParseResult> {
    let lex_result = db.lex(file, split)?;
    let text = db.split(file, split)?.text;
    let mut parser = Parser {
        text: text.slice(..),
        builder: GreenNodeBuilder::new(),
        lex_result: &lex_result,
        tok_idx: 0,
        errors: Vec::new(),
    };
    parser.builder.start_node(Tok::Root.into());
    parser.defs();
    parser.builder.finish_node();
    let Parser {
        errors, builder, ..
    } = parser;
    let mut errors: Vec<_> = errors.into_iter().map(|(x, s)| x.to_error(s)).collect();
    errors.extend(
        lex_result
            .error
            .into_iter()
            .map(|(x, s)| super::lexer::lexerror_to_error(x, s)),
    );
    Some(ParseResult {
        errors,
        green: builder.finish(),
    })
}

// Precedence machinery

/// A precedence group, a group of binary operators with the same grouping behavior.
/// Precedence is a partial order, which is why `Prec` only implements `PartialOrd`.
#[derive(Clone, Copy, Hash, Eq, PartialEq)]
enum Prec {
    /// and, or
    Logic,
    /// ->
    Arrow,
    /// +, -
    AddSub,
    /// *, /, %
    MulDiv,
    /// **
    Exp,
    /// &, |, ^^, >>, <<
    Bitwise,
    /// >, >=, <, <=, ==, !=
    Comp,
    /// |>, <|
    Pipe,
    /// f a b
    App,
    /// if (not a real binop)
    If,
    /// Synthetic minimum precedence to allow all operators
    Min,
}
impl Prec {
    /// The precedence of comparison operators, used by `Prec::Bitwise` because it has higher precedence than this and below.
    const COMP_PREC: usize = 2;

    /// If this is one of the precedence levels used in arithmetic, which have a total order between them, returns that level as a `usize`.
    fn arith_prec(self) -> Option<usize> {
        match self {
            Prec::Pipe => Some(0),
            Prec::Logic => Some(1),
            Prec::Comp => Some(2),
            Prec::AddSub => Some(3),
            Prec::MulDiv => Some(4),
            Prec::Exp => Some(5),
            _ => None,
        }
    }
}
impl PartialOrd for Prec {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Prec::Min, Prec::Min) => return Some(Ordering::Equal),
            (Prec::Min, _) => return Some(Ordering::Less),
            (_, Prec::Min) => return Some(Ordering::Greater),
            // Application has the highest precedence
            (Prec::App, Prec::App) => return Some(Ordering::Equal),
            (Prec::App, _) => return Some(Ordering::Greater),
            (_, Prec::App) => return Some(Ordering::Less),
            // And if has the lowest precedence
            (Prec::If, Prec::If) => return Some(Ordering::Equal),
            (Prec::If, _) => return Some(Ordering::Less),
            (_, Prec::If) => return Some(Ordering::Greater),
            _ => (),
        }
        match (self.arith_prec(), other.arith_prec()) {
            (Some(a), Some(b)) => return a.partial_cmp(&b),

            // Bitwise operators are higher precedence than comparison and logic, but can't be mixed with arithmetic operators
            (Some(a), _) if *other == Prec::Bitwise => {
                if a <= Prec::COMP_PREC {
                    return Some(Ordering::Less);
                } else {
                    return None;
                }
            }
            (_, Some(b)) if *self == Prec::Bitwise => {
                if b <= Prec::COMP_PREC {
                    return Some(Ordering::Greater);
                } else {
                    return None;
                }
            }

            _ => (),
        }
        None
    }
}

impl Tok {
    /// Whether this token can end an argument list.
    /// True for arrows, and things that can come after `fun` or constructor arguments.
    fn ends_args(&self) -> bool {
        matches!(
            self,
            Tok::WideArrow
                | Tok::Arrow
                | Tok::Equals
                | Tok::Colon
                | Tok::POpen
                | Tok::SOpen
                | Tok::OfKw
                | Tok::Newline
                | Tok::Dedent
                | Tok::Indent
                | Tok::WithKw
        )
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self,
            Tok::Name
                | Tok::IntLit
                | Tok::FloatLit
                | Tok::POpen
                | Tok::StructKw
                | Tok::SigKw
                | Tok::TypeTypeKw
                | Tok::CaseKw
                | Tok::CatchKw
                | Tok::COpen
                | Tok::DoKw
                | Tok::StringLit
        )
    }

    /// Whether this token and another token can be used together left-associatively in expressions like `a + b - c`.
    /// Arithmetic operators return `true` if `other` has the same precedence; otherwise, most return `false`.
    fn associates_with(&self, other: &Tok) -> bool {
        // Arithmetic operators associate with each other if they have the same precedence
        if let Some(p) = self.binop_prec().and_then(|x| x.arith_prec()) {
            if p > Prec::COMP_PREC {
                return other
                    .binop_prec()
                    .and_then(|x| x.arith_prec())
                    .map_or(false, |p2| p2 == p);
            }
        }
        // Bitwise operators only associate with themselves
        if let Some(Prec::Bitwise) = self.binop_prec() {
            return self == other;
        }
        match (self, other) {
            // a.b.c = (a.b).c
            (Tok::Dot, Tok::Dot)
            // a and b and c = (a and b) and c = a and (b and c)
            | (Tok::AndKw, Tok::AndKw)
            // same for or
            | (Tok::OrKw, Tok::OrKw)
            // a |> f |> g = (a |> f) |> g
            | (Tok::RPipe, Tok::RPipe)
            // f <| a <| b = (f <| a) <| b
            | (Tok::LPipe, Tok::LPipe) => true,
            // Arrows are right associative, so they get special casing in term()
            // Everything else is non-associative
            _ => false,
        }
    }

    /// If this token is a binary operator, returns its precedence group; otherwise, returns `None`.
    fn binop_prec(&self) -> Option<Prec> {
        Some(match self {
            Tok::AndKw | Tok::OrKw => Prec::Logic,
            Tok::Arrow => Prec::Arrow,
            Tok::Plus | Tok::Minus => Prec::AddSub,
            Tok::Times | Tok::Mod | Tok::Div => Prec::MulDiv,
            Tok::Exp => Prec::Exp,
            Tok::Bar | Tok::Xor | Tok::LShift | Tok::RShift | Tok::BitAnd => Prec::Bitwise,
            Tok::Gt | Tok::GtE | Tok::Lt | Tok::LtE | Tok::Eq | Tok::NEq => Prec::Comp,
            Tok::Comma => return None,
            Tok::LPipe | Tok::RPipe => Prec::Pipe,
            Tok::ElseKw => Prec::Pipe,
            _ => return None,
        })
    }
}
