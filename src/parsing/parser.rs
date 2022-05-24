use std::cmp::Ordering;

use ropey::RopeSlice;
use rowan::{Checkpoint, GreenNode, GreenNodeBuilder};

use super::{lexer::*, SplitId};
use crate::common::*;

enum ParseError {
    Expected(Cow<'static, str>, Option<Cow<'static, str>>),
    Unexpected(Cow<'static, str>, Option<Cow<'static, str>>),
    Other(Cow<'static, str>),
}
impl ParseError {
    fn to_error(self, span: RelSpan) -> Error {
        let mut gen = ariadne::ColorGenerator::default();
        let _ = gen.next();
        let a = gen.next();
        let message = match self {
            ParseError::Expected(t, None) => {
                Doc::start("expected ").add(t, a).space().add("here", ())
            }
            ParseError::Expected(t, Some(m)) => {
                Doc::start("expected ").add(t, a).space().add(m, ())
            }
            ParseError::Unexpected(t, None) => {
                Doc::start("unexpected ").add(t, a).space().add("here", ())
            }
            ParseError::Unexpected(t, Some(m)) => {
                Doc::start("unexpected ").add(t, a).space().add(m, ())
            }
            ParseError::Other(m) => Doc::start(m),
        };
        Error {
            severity: Severity::Error,
            message: message.clone(),
            primary: Label {
                span,
                message,
                color: Some(a),
            },
            secondary: Vec::new(),
            note: None,
        }
    }
}

trait IntoMsg {
    fn into_msg(self) -> Option<Cow<'static, str>>;
}
trait X {}
impl<T: Into<Cow<'static, str>> + X> IntoMsg for T {
    fn into_msg(self) -> Option<Cow<'static, str>> {
        Some(self.into())
    }
}
impl X for &'static str {}
impl X for String {}
impl IntoMsg for Option<Cow<'static, str>> {
    fn into_msg(self) -> Option<Cow<'static, str>> {
        self
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
        let end = self
            .lex_result
            .start
            .get(self.tok_idx + 1)
            .copied()
            .unwrap_or_else(|| self.text.len_chars() as u32);
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

    fn peek(&self, num_ahead: usize) -> Tok {
        self.lex_result
            .kind
            .get(self.tok_idx + num_ahead)
            .copied()
            .unwrap_or(Tok::Eof)
    }

    fn tok_span(&self) -> RelSpan {
        let start = self.lex_result.start[self.tok_idx];
        let end = self
            .lex_result
            .start
            .get(self.tok_idx + 1)
            .copied()
            .unwrap_or_else(|| self.text.len_chars() as u32);
        start..end
    }

    fn expected(&mut self, x: impl Into<Cow<'static, str>>, m: impl IntoMsg) {
        let span = self.tok_span();
        self.errors
            .push((ParseError::Expected(x.into(), m.into_msg()), span));
    }

    fn expect(&mut self, t: Tok) -> bool {
        if self.cur() != t {
            self.expected(t.to_string(), None);
            false
        } else {
            self.advance();
            true
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
            self.expected("newline", " or end of definitions");
        }
    }

    fn def(&mut self) {
        match self.cur() {
            Tok::FunKw => {
                self.push(Tok::FunDef);
                self.advance();

                self.var();

                self.params(true);

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

                self.params(true);

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

                        self.params(false);

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
            Tok::LetKw => {
                self.push(Tok::LetDef);
                self.advance();

                self.push(Tok::Pat);
                self.expr(());
                self.pop();

                self.expect(Tok::Equals);

                self.push(Tok::Body);
                self.expr(());
                self.pop();

                self.pop();
                self.def_end();
            }
            _ => {
                self.expected("definition", None);
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
            Tok::TypeTypeKw => {
                self.push(Tok::Type);
                self.advance();
                self.pop();
            }
            tok => {
                self.expected("expression", None);
                if tok.starts_atom() {
                    self.advance();
                }
            }
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

    fn params_inner(&mut self) -> Checkpoint {
        // First implicit params
        let cp = self.checkpoint();
        let mut had_imp = false;
        while self.cur() == Tok::SOpen {
            had_imp = true;
            self.push(Tok::ImpPar);
            self.push(Tok::PatPar);
            self.push(Tok::Pat);

            self.advance();
            self.expr(());
            self.expect(Tok::SClose);

            self.pop();
            self.pop();
            self.pop();
        }
        if had_imp {
            self.push_at(cp, Tok::ImpPars);
            self.pop();
        }

        // Then explicit
        let cp = self.checkpoint();
        self.atom();
        cp
    }

    fn params(&mut self, pat: bool) {
        let cp = self.params_inner();
        if pat {
            self.push_at(cp, Tok::PatPar);
            self.push_at(cp, Tok::Pat);
            self.pop();
        } else {
            self.push_at(cp, Tok::TermPar);
        }
        self.pop();
    }

    fn arguments(&mut self) {
        // First implicit args
        let cp = self.checkpoint();
        let mut had_imp = false;
        while self.cur() == Tok::SOpen {
            had_imp = true;
            self.push(Tok::ImpArg);
            self.advance();
            self.expr(());
            self.expect(Tok::SClose);
            self.pop();
        }
        if had_imp {
            self.push_at(cp, Tok::ImpArgs);
            self.pop();
        }

        // Then explicit
        if self.cur().starts_atom() {
            self.atom();
        }
    }

    fn argument_block(&mut self) {
        // Implicit arguments
        let cp = self.checkpoint();
        let mut had_imp = false;
        while self.cur() == Tok::SOpen {
            had_imp = true;
            self.push(Tok::ImpArg);
            self.advance();
            self.expr(());
            self.expect(Tok::SClose);
            self.pop();
            self.maybe(Tok::Newline);
        }
        if had_imp {
            self.push_at(cp, Tok::ImpArgs);
            self.pop();
        }

        // Explicit
        if !had_imp || self.cur().starts_atom() {
            let mut cp = self.checkpoint();
            let mut ntuples = 0;
            loop {
                let cp2 = self.checkpoint();
                self.expr(());
                if self.maybe(Tok::Comma) {
                    match self.cur() {
                        Tok::Newline => {
                            self.push_at(cp, Tok::Tuple);
                            ntuples += 1;
                            cp = cp2;
                            self.advance()
                        }
                        Tok::Dedent => {
                            self.advance();
                            break;
                        }
                        _ => {
                            self.expected("newline or dedent", "after comma");
                            while !matches!(self.cur(), Tok::Newline | Tok::Dedent | Tok::Eof) {
                                self.advance();
                            }
                            if self.maybe(Tok::Newline) {
                                continue;
                            } else {
                                self.advance();
                                break;
                            }
                        }
                    }
                } else {
                    if !self.maybe(Tok::Dedent) {
                        self.expected("dedent, or comma", "to continue argument list");
                        if self.maybe(Tok::Newline) {
                            // Pretend there was a comma
                            self.push_at(cp, Tok::Tuple);
                            ntuples += 1;
                            cp = cp2;
                            continue;
                        } else {
                            while !self.maybe(Tok::Dedent) {
                                self.advance();
                            }
                        }
                    }
                    break;
                }
            }
            for _ in 0..ntuples {
                self.pop();
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
                    Tok::Colon if Prec::Binder > min_prec => {
                        self.push(Tok::Binder);

                        self.advance();
                        self.push(Tok::Ty);
                        self.expr(Prec::Binder);
                        self.pop();

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
                    // If it starts with [, it must be a lambda or pi
                    Tok::SOpen => {
                        let par_cp = self.params_inner();
                        match self.cur() {
                            Tok::WideArrow => {
                                self.push_at(cp, Tok::Lam);

                                self.push_at(par_cp, Tok::PatPar);
                                self.push_at(par_cp, Tok::Pat);
                                self.pop();
                                self.pop();

                                self.advance();

                                self.push(Tok::Body);
                                self.expr(());
                                self.pop();

                                self.pop();
                            }
                            Tok::Arrow => {
                                self.push_at(cp, Tok::Pi);

                                self.push_at(par_cp, Tok::TermPar);
                                self.pop();

                                self.advance();

                                self.push(Tok::Body);
                                self.expr(Prec::Arrow);
                                self.pop();

                                self.maybe_with();

                                self.pop();
                            }
                            _ => {
                                self.expected("-> or =>", "after implicit parameters");
                                self.advance();
                            }
                        }
                    }
                    _ => self.atom(),
                }
                cp
            }
            Some(cp) => cp,
        };

        loop {
            match self.cur() {
                Tok::SOpen | Tok::POpen => {
                    self.push_at(lhs, Tok::App);
                    self.arguments();
                    self.pop();
                }

                x if x.starts_atom() => {
                    self.push_at(lhs, Tok::App);
                    self.arguments();
                    self.pop();
                }
                Tok::Dot => {
                    self.push_at(lhs, Tok::App);
                    self.advance();

                    self.push(Tok::Member);
                    self.var();
                    self.pop();

                    if self.maybe(Tok::Indent) {
                        self.argument_block();
                    } else {
                        self.arguments();
                    }
                    self.pop();
                }
                // , is right associative
                Tok::Comma if Prec::Comma >= min_prec => {
                    // Trailing comma special case
                    if matches!(self.peek(1), Tok::Newline | Tok::Dedent) {
                        return;
                    }

                    self.push_at(lhs, Tok::Tuple);

                    self.advance();
                    self.expr(Prec::Comma);

                    self.pop();
                }
                // : is non-associative
                Tok::Colon if Prec::Binder > min_prec => {
                    self.push_at(lhs, Tok::Binder);
                    self.push_at(lhs, Tok::Pat);
                    self.pop();

                    self.advance();
                    self.push(Tok::Ty);
                    self.expr(Prec::Binder);
                    self.pop();

                    self.pop();
                }
                // This indent appears before an operator (inc. application)
                // So implement operator chaining
                // If we're not at the outermost expression, though, pass control back there
                Tok::Indent => {
                    if min_prec == Prec::Min {
                        self.advance();
                        loop {
                            // Handle application
                            if self.cur().starts_atom() || self.cur() == Tok::SOpen {
                                self.push_at(lhs, Tok::App);
                                self.argument_block();
                                self.pop();
                                break;
                            }
                            // Each line has an operator + rhs, then a newline
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
                                    self.expected("dedent", None);
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
                    self.push_at(lhs, Tok::Lam);

                    self.push_at(lhs, Tok::PatPar);
                    self.push_at(lhs, Tok::Pat);
                    self.pop();
                    self.pop();

                    self.advance();

                    self.push(Tok::Body);
                    self.expr(());
                    self.pop();

                    self.pop();
                }
                Tok::Arrow if Prec::Arrow >= min_prec => {
                    self.push_at(lhs, Tok::Pi);

                    self.push_at(lhs, Tok::TermPar);
                    self.pop();

                    self.advance();

                    self.push(Tok::Body);
                    self.expr(Prec::Arrow);
                    self.pop();

                    self.maybe_with();

                    self.pop();
                }
                op if op.binop_prec().is_some() => {
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

#[derive(Debug, Clone, PartialEq, Eq)]
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
    /// ,
    Comma,
    /// :
    Binder,
    /// Synthetic minimum precedence to allow all operators
    Min,
}
impl Prec {
    /// The precedence of comparison operators, used by `Prec::Bitwise` because it has higher precedence than this and below.
    const COMP_PREC: usize = 2;

    /// If this is one of the precedence levels used in arithmetic, which have a total order between them, returns that level as a `usize`.
    fn arith_prec(self) -> Option<usize> {
        match self {
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
            // Next is pipe
            (Prec::Pipe, Prec::Pipe) => return Some(Ordering::Equal),
            (Prec::Pipe, _) => return Some(Ordering::Less),
            (_, Prec::Pipe) => return Some(Ordering::Greater),
            // Next lowest precedence is comma, then binder
            (Prec::Comma, Prec::Comma) => return Some(Ordering::Equal),
            (Prec::Comma, _) => return Some(Ordering::Less),
            (_, Prec::Comma) => return Some(Ordering::Greater),
            (Prec::Binder, Prec::Binder) => return Some(Ordering::Equal),
            (Prec::Binder, _) => return Some(Ordering::Less),
            (_, Prec::Binder) => return Some(Ordering::Greater),
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