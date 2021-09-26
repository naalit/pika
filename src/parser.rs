use crate::common::*;
use crate::error::{Span, Spanned};
use crate::lexer::*;
use crate::term::*;
use std::cmp::Ordering;

type PResult<T> = Result<T, Spanned<LexError>>;

pub struct Parser<'i> {
    lexer: Lexer<'i>,
    buf: Option<(usize, Tok<'i>, usize)>,
    pending_err: Option<Spanned<LexError>>,
    db: &'i dyn Compiler,
}
/// Utilities
impl<'i> Parser<'i> {
    pub fn new(db: &'i dyn Compiler, lexer: Lexer<'i>) -> Self {
        Parser {
            lexer,
            buf: None,
            pending_err: None,
            db,
        }
    }

    fn span(&mut self) -> Span {
        match self.peek_() {
            Some((a, _, b)) => Span(a, b),
            None => self.lexer.span(),
        }
    }

    fn peek_(&mut self) -> Option<(usize, Tok<'i>, usize)> {
        if self.pending_err.is_some() {
            return None;
        }
        match &self.buf {
            Some(t) => Some(t.clone()),
            None => {
                match self.lexer.next() {
                    Some(Ok(t)) => self.buf = Some(t),
                    Some(Err(e)) => self.pending_err = Some(e),
                    None => (),
                }
                self.buf.clone()
            }
        }
    }

    fn has_next(&mut self) -> bool {
        self.peek_().is_some()
    }

    // Look at the current token, but don't consume it.
    // The parser uses only 1-token lookahead.
    fn peek(&mut self, eof_expected: &str) -> PResult<Tok<'i>> {
        let t = self.peek_();
        if let Some(e) = self.pending_err.clone() {
            Err(e)
        } else {
            t.map(|(_, t, _)| t).ok_or_else(|| {
                Spanned::new(
                    LexError::Other(format!(
                        "Unexpected end of input, expected {}",
                        eof_expected
                    )),
                    self.lexer.span(),
                )
            })
        }
    }

    fn next(&mut self) -> Option<Tok<'i>> {
        let t = self.buf.take();
        self.peek_();
        t.map(|(_, t, _)| t)
    }

    fn err<T, U: Into<String>>(&mut self, msg: U) -> PResult<T> {
        let span = self.lexer.span();
        PResult::Err(Spanned::new(LexError::Other(msg.into()), span))
    }

    fn unexpected<T>(&mut self, tok: Tok<'i>, expected: &str) -> PResult<T> {
        // panic!("unexpected {}, expected {}", tok, expected);
        self.err(format!("unexpected {}, expected {}", tok, expected))
    }

    fn maybe(&mut self, tok: Tok<'i>) -> bool {
        if self.peek("") == Ok(tok) {
            self.next();
            true
        } else {
            false
        }
    }
}

/// Parsing
impl<'i> Parser<'i> {
    /// Parse top-level definitions until the end of the input.
    pub fn defs(&mut self) -> PResult<Vec<PreDefAn>> {
        let mut v = Vec::new();
        self.maybe(Tok::Newline);
        while self.has_next() {
            v.push(self.def()?);
        }
        if let Some(err) = self.pending_err.take() {
            Err(err)
        } else {
            Ok(v)
        }
    }

    /// Consume one or more newlines or semicolons, or peek a dedent or EOF.
    fn def_end(&mut self) -> PResult<()> {
        match self.peek("newline") {
            Ok(Tok::Newline) => {
                self.next();
                Ok(())
            }
            Ok(Tok::Dedent) | Err(_) => Ok(()),
            Ok(t) => self.unexpected(t, "newline or end of definitions"),
        }
    }

    #[must_use = "don't forget to dedent"]
    fn indent_or_newline(&mut self, indent: bool) -> bool {
        if indent {
            self.maybe(Tok::Newline);
            indent
        } else {
            self.maybe(Tok::Indent)
        }
    }

    /// Consume a token, and give an error if it doesn't match the provided token.
    fn expect(&mut self, tok: Tok<'i>) -> PResult<Spanned<Tok<'i>>> {
        let span = self.span();
        let t = self.next();
        if let Some(e) = self.pending_err.clone() {
            return Err(e);
        }
        if t.as_ref() != Some(&tok) {
            if let Some(ty) = tok.closes_type() {
                Err(Spanned::new(LexError::MissingTerminator(ty), span))
            } else if let Some(t) = t {
                self.unexpected(t, &format!("{}", tok))
            } else {
                self.err(format!("unexpected end of input, expected {}", tok))
            }
        } else {
            Ok(Spanned::new(t.unwrap(), span))
        }
    }

    fn def(&mut self) -> PResult<PreDefAn> {
        match self.peek("definition")? {
            Tok::At => {
                // Consume the @
                self.next();

                // Parse an attribute
                self.expect(Tok::SOpen)?;
                let aspan = self.span();
                let attr = match self.next() {
                    Some(Tok::Name(n)) => {
                        Attribute::parse(n).map_err(|x| Spanned::new(LexError::Other(x), aspan))
                    }
                    Some(t) => self.unexpected(t, "attribute name"),
                    None => self.err("unexpected end of input, expected attribute name"),
                }?;
                self.expect(Tok::SClose)?;

                self.maybe(Tok::Newline);

                let mut def = self.def()?;
                def.attributes.push(attr);
                Ok(def)
            }
            Tok::Val => {
                // Consume the `val`
                self.next();
                let i_name = self.maybe(Tok::Indent);

                let name = self.name()?;

                let i_colon = self.maybe(Tok::Indent);
                let ty = if let Tok::Colon = self.peek("=")? {
                    // Consume the :
                    self.next();

                    let t = self.term()?;
                    if i_colon {
                        self.maybe(Tok::Newline);
                    }
                    t
                } else {
                    Spanned::new(Pre_::Hole(MetaSource::LocalType(*name)), name.span())
                };

                let r = match self.peek("=")? {
                    Tok::Equals => {
                        self.next();
                        let i_body = self.maybe(Tok::Indent);
                        let body = self.term()?;
                        if i_body {
                            self.expect(Tok::Dedent)?;
                        }

                        Ok(PreDef::Val(name, ty, body).into())
                    }
                    Tok::Newline | Tok::Dedent => Ok(PreDef::ValDec(name, ty).into()),
                    t => self.unexpected(t, "="),
                }?;

                if i_colon {
                    self.expect(Tok::Dedent)?;
                }
                if i_name {
                    self.expect(Tok::Dedent)?;
                }

                self.def_end()?;

                Ok(r)
            }
            Tok::Fun => {
                // Consume the `fun`
                self.next();

                let name = self.name()?;

                let indent = self.maybe(Tok::Indent);
                let mut args = Vec::new();
                self.args(&mut args, &mut ArgMode::FunDef, indent)?;
                let args = args
                    .into_iter()
                    .map(|(n, i, t)| {
                        let t =
                            t.unwrap_or_else(|| n.copy_span(Pre_::Hole(MetaSource::LocalType(*n))));
                        (*n, i, t)
                    })
                    .collect();

                let indent = self.indent_or_newline(indent);
                let ty = if let Tok::Colon = self.peek("=")? {
                    // Consume the :
                    self.next();

                    self.term()?
                } else {
                    Spanned::new(Pre_::Hole(MetaSource::LocalType(*name)), name.span())
                };

                let indent = self.indent_or_newline(indent);
                let effs = self.maybe_effs_list()?;

                let r = match self.peek("=")? {
                    Tok::Equals => {
                        self.next();
                        let i_body = self.maybe(Tok::Indent);
                        let body = self.term()?;
                        if i_body {
                            self.expect(Tok::Dedent)?;
                        }

                        // TODO: do we ever infer effects? Maybe if no return type is given?
                        Ok(PreDef::Fun(name, args, ty, body, Some(effs)).into())
                    }
                    Tok::Newline => Ok(PreDef::FunDec(name, args, ty, Some(effs)).into()),
                    t => self.unexpected(t, "="),
                }?;

                if indent {
                    self.expect(Tok::Dedent)?;
                }

                self.def_end()?;

                Ok(r)
            }
            Tok::Type | Tok::Eff => {
                // Consume the `type` or `eff`
                let is_eff = match self.next().unwrap() {
                    Tok::Type => false,
                    Tok::Eff => true,
                    _ => unreachable!(),
                };

                let name = self.name()?;

                let mut indent = self.maybe(Tok::Indent);
                let mut ty_args = Vec::new();
                self.args(&mut ty_args, &mut ArgMode::FunDef, indent)?;
                let ty_args: Vec<_> = ty_args
                    .into_iter()
                    .map(|(n, i, t)| {
                        let t =
                            t.unwrap_or_else(|| n.copy_span(Pre_::Hole(MetaSource::LocalType(*n))));
                        (*n, i, t)
                    })
                    .collect();

                // Consume the `of` or `=`
                let short = match self.peek("'of'")? {
                    // type Option
                    //     a
                    // of
                    Tok::Dedent if indent => {
                        self.next();
                        self.expect(Tok::Newline)?;
                        self.expect(Tok::Of)?;
                        indent = false;
                        false
                    }
                    // type Option a of
                    Tok::Of if !indent => {
                        self.next();
                        false
                    }
                    // type Pair a = (a, b)
                    Tok::Equals => {
                        self.next();
                        true
                    }
                    // type Pair a
                    //     = (a, b)
                    Tok::Indent if !indent => {
                        self.next();
                        self.expect(Tok::Equals)?;
                        indent = true;
                        true
                    }
                    // type Pair
                    //     a
                    //     = (a, b)
                    Tok::Newline if indent => {
                        self.next();
                        self.expect(Tok::Equals)?;
                        true
                    }
                    t => return self.unexpected(t, "'of'"),
                };

                let ctors = if short {
                    // Short form

                    // type Pair a =
                    //   (a, b)
                    let i_body = self.maybe(Tok::Indent);
                    let term = self.term()?;
                    if i_body {
                        self.expect(Tok::Dedent)?;
                    }
                    PreDataType::ShortForm(term)
                } else {
                    // Long form

                    // indent after `of`
                    self.expect(Tok::Indent)?;

                    // Now the constructors
                    let mut ctors = Vec::new();
                    loop {
                        let name = self.name()?;

                        let indent = self.maybe(Tok::Indent);
                        let mut args = Vec::new();
                        self.args(&mut args, &mut ArgMode::Cons, indent)?;
                        let args: Vec<_> = args
                            .into_iter()
                            .map(|(n, i, t)| {
                                let t = t.unwrap_or_else(|| {
                                    n.copy_span(Pre_::Hole(MetaSource::LocalType(*n)))
                                });
                                (*n, i, t)
                            })
                            .collect();

                        let indent = self.indent_or_newline(indent);
                        let ty = if self.peek("_") == Ok(Tok::Colon) {
                            // Consume the :
                            self.next();

                            Some(self.term()?)
                        } else {
                            None
                        };

                        if indent {
                            self.expect(Tok::Dedent)?;
                        }

                        ctors.push(PreCons(name, args, ty));
                        if !self.maybe(Tok::Newline) {
                            break;
                        }
                    }

                    self.expect(Tok::Dedent)?;
                    PreDataType::Standard(ctors)
                };

                if indent {
                    self.expect(Tok::Dedent)?;
                }
                let done = self.def_end().is_ok();

                // Do the associated namespace
                let mut namespace = Vec::new();
                if self.peek("_") == Ok(Tok::Where) {
                    self.next();
                    self.expect(Tok::Indent)?;

                    while !matches!(self.peek("_"), Err(_) | Ok(Tok::Dedent)) {
                        namespace.push(self.def()?);
                    }

                    self.expect(Tok::Dedent)?;
                    self.def_end()?;
                } else if !done {
                    self.def_end()?;
                }

                Ok(PreDef::Type {
                    name,
                    is_eff,
                    ty_args,
                    ctors,
                    namespace,
                }
                .into())
            }
            _ => {
                // We don't allow lambdas in expression statements, so the multiline lambda syntax is unambiguous
                let term = self.term()?;
                self.def_end()?;
                Ok(PreDef::Expr(term).into())
            }
        }
    }

    fn maybe_effs_list(&mut self) -> PResult<Vec<Pre>> {
        if let Ok(Tok::With) = self.peek("_") {
            // Consume the `with`
            self.next();

            let mut v = Vec::new();
            loop {
                let eff = self.term()?;
                v.push(eff);
                if let Ok(Tok::Comma) = self.peek("_") {
                    self.next();
                } else {
                    break Ok(v);
                }
            }
        } else {
            Ok(Vec::new())
        }
    }

    /// Parse a top-level expression - a lambda or pi type, plus anything parsed by `binop()`.
    fn term(&mut self) -> PResult<Pre> {
        ExprParser::new(self, false).go()
    }

    /// Parse the arguments of a function-like structure, starting with the given arguments and the given possible modes.
    /// This function will add the arguments to `args`, and only change `mode` if `arg_group()` does.
    fn args(
        &mut self,
        args: &mut Vec<(SName, Icit, Option<PreTy>)>,
        mode: &mut ArgMode,
        indented: bool,
    ) -> PResult<()> {
        ExprParser::new(self, false).args(args, mode, indented)
    }

    /// Parse any expression which has a well-defined start and end, and so can be a component of an application.
    /// This includes things like names and numbers, as well as parenthesized expressions and expressions with `end`.
    ///
    /// This function will actually also parse `if` expressions, which won't end until the parent context ends, so aren't technically atoms.
    /// For example,
    /// ```text
    /// if cond then 1 else 2
    ///   + 3
    /// ```
    /// is equivalent to
    /// ```text
    /// if cond then 1 else (2 + 3)
    /// ```
    // TODO is that actually what we want? It conflicts with the thing where binops group preceding lines
    fn atom(&mut self) -> PResult<Pre> {
        match self.peek("expression")? {
            Tok::POpen => {
                let start = self.span().0;
                self.next();

                if self.peek("_") == Ok(Tok::PClose) {
                    let end = self.span().1;
                    self.next();
                    return Ok(Spanned::new(Pre_::Unit, Span(start, end)));
                }

                let ret = self.term()?;

                self.maybe(Tok::Newline);
                self.expect(Tok::PClose)?;

                Ok(ret)
            }
            Tok::Name(_) => {
                let name = self.name()?;
                Ok(Spanned::new(Pre_::Var(*name), name.span()))
            }
            Tok::String(n) => {
                let name = self.db.intern_name(n);
                let r = Ok(Spanned::new(Pre_::Lit(Literal::String(name)), self.span()));
                self.next();
                r
            }
            Tok::Lit(l) => {
                let span = self.span();
                self.next();
                Ok(Spanned::new(Pre_::Lit(l), span))
            }
            Tok::TypeType => {
                let span = self.span();
                self.next();
                Ok(Spanned::new(Pre_::Type, span))
            }
            Tok::Do | Tok::Struct | Tok::Sig => {
                let start = self.span().0;
                let tok = self.next();
                self.expect(Tok::Indent)?;

                let mut v = Vec::new();

                while self.peek("").map_or(false, |x| x != Tok::Dedent) {
                    v.push(self.def()?);
                }

                let end = self.span().0;
                self.expect(Tok::Dedent)?;

                Ok(Spanned::new(
                    match tok.unwrap() {
                        Tok::Do => Pre_::Do(v),
                        Tok::Struct => Pre_::Struct(v),
                        Tok::Sig => Pre_::Sig(v),
                        _ => unreachable!(),
                    },
                    Span(start, end),
                ))
            }
            Tok::Case | Tok::Catch => {
                let start = self.span().0;
                let is_catch = match self.next().unwrap() {
                    Tok::Case => false,
                    Tok::Catch => true,
                    _ => unreachable!(),
                };

                // catch
                //     something long ...
                // of
                let i_scrutinee = self.maybe(Tok::Indent);
                let scrutinee = self.term()?;
                if i_scrutinee {
                    self.expect(Tok::Dedent)?;
                }
                // allow a newline even without indentation for:
                // catch do
                //     ...
                // of
                self.maybe(Tok::Newline);

                self.expect(Tok::Of)?;
                self.expect(Tok::Indent)?;

                let mut v = Vec::new();

                loop {
                    let pat = self.pat()?;
                    self.expect(Tok::WideArrow)?;
                    let body = self.term()?;

                    v.push((pat, body));

                    if !self.maybe(Tok::Newline) {
                        break;
                    }
                }

                let end = self.span().0;
                self.expect(Tok::Dedent)?;

                Ok(Spanned::new(
                    Pre_::Case(is_catch, scrutinee, v),
                    Span(start, end),
                ))
            }
            t => self.unexpected(t, "expression"),
        }
    }

    fn pat(&mut self) -> PResult<Pre> {
        match self.peek("pattern")? {
            Tok::Eff => {
                let start = self.span().0;
                self.next();
                let p = self.atom()?;
                let k = self.atom()?;

                let end = k.span().1;
                let span = Span(start, end);
                Ok(Spanned::new(Pre_::EffPat(p, k), span))
            }
            _ => ExprParser::new(self, true).go(),
        }
    }

    /// Parses just a name, interning it and returning it with its span.
    fn name(&mut self) -> PResult<Spanned<Name>> {
        let tok = self.peek("name")?;
        if let Tok::Name(n) = tok {
            let span = self.span();
            self.next();
            Ok(Spanned::new(self.db.intern_name(n.to_string()), span))
        } else {
            self.unexpected(tok, "name")
        }
    }
}

/// A grammatical structure than has parameters.
/// Each grammatical structure has slightly different rules for parameter syntax, so the parser needs to know which one it's parsing.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ArgMode {
    FunDef,
    Lambda,
    Pi,
    /// Either a pi type or a lambda - we won't know until we get to the arrow, or an expression as the last parameter to the pi type.
    PiOrLambda,
    Cons,
}
impl ArgMode {
    /// If `self` is `PiOrLambda`, switches to `Lambda`.
    /// If `self` is `Pi`, returns `false`.
    fn not_pi(&mut self) -> bool {
        if *self == ArgMode::PiOrLambda {
            *self = ArgMode::Lambda;
        }
        *self != ArgMode::Pi
    }

    /// If `self` is `PiOrLambda`, switches to `Pi`.
    /// If `self` is incompatible with `Pi`, returns `false`.
    fn yes_pi(&mut self) -> bool {
        match *self {
            ArgMode::PiOrLambda => {
                *self = ArgMode::Pi;
                true
            }
            ArgMode::Pi => true,
            _ => false,
        }
    }

    /// A string representing the kind of parameter we're looking for, for use with `Parser::unexpected()`.
    /// For example, `"function parameter"`.
    fn str(self) -> &'static str {
        match self {
            ArgMode::FunDef => "function parameter",
            ArgMode::Cons => "constructor parameter",
            ArgMode::Lambda => "lambda parameter",
            ArgMode::Pi => "pi type parameter",
            ArgMode::PiOrLambda => "lambda or pi type parameter",
        }
    }
}

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
            // Application has the highest precedence
            (Prec::App, Prec::App) => return Some(Ordering::Equal),
            (Prec::App, _) => return Some(Ordering::Greater),
            (_, Prec::App) => return Some(Ordering::Less),
            // And if has the lowest precedence
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

impl<'i> Tok<'i> {
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
                | Tok::Of
                | Tok::Newline
                | Tok::Dedent
                | Tok::Indent
                | Tok::With
        )
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self,
            Tok::Name(_)
                | Tok::Lit(_)
                | Tok::POpen
                | Tok::Struct
                | Tok::Sig
                | Tok::TypeType
                | Tok::Case
                | Tok::Catch
                | Tok::COpen
                | Tok::Do
                | Tok::String(_)
        )
    }

    /// Whether this token and another token can be used together left-associatively in expressions like `a + b - c`.
    /// Arithmetic operators return `true` if `other` has the same precedence; otherwise, most return `false`.
    fn associates_with(&self, other: &Tok<'i>) -> bool {
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
            | (Tok::And, Tok::And)
            // same for or
            | (Tok::Or, Tok::Or)
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
            Tok::And | Tok::Or => Prec::Logic,
            Tok::Arrow => Prec::Arrow,
            Tok::Plus | Tok::Minus => Prec::AddSub,
            Tok::Times | Tok::Mod | Tok::Div => Prec::MulDiv,
            Tok::Exp => Prec::Exp,
            Tok::Bar | Tok::Xor | Tok::LShift | Tok::RShift | Tok::BitAnd => Prec::Bitwise,
            Tok::Gt | Tok::GtE | Tok::Lt | Tok::LtE | Tok::Eq | Tok::NEq => Prec::Comp,
            Tok::Comma => return None,
            Tok::LPipe | Tok::RPipe => Prec::Pipe,
            Tok::Else => Prec::Pipe,
            _ => return None,
        })
    }
}

#[derive(Clone, Debug)]
enum Op<'i> {
    Tok(Spanned<Tok<'i>>),
    App(Icit),
    If(Option<Pre>),
}
impl<'i> Op<'i> {
    fn binop_prec(&self) -> Prec {
        match self {
            Op::Tok(i) => i.binop_prec().unwrap(),
            Op::App(_) => Prec::App,
            Op::If(_) => Prec::If,
        }
    }

    fn associates_with(&self, other: &Self) -> bool {
        match (self, other) {
            (Op::Tok(a), Op::Tok(b)) => a.associates_with(b),
            (Op::App(_), Op::App(_)) => true,
            _ => false,
        }
    }
}
impl<'i> std::fmt::Display for Op<'i> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Op::Tok(t) => write!(f, "{}", **t),
            Op::App(_) => write!(f, "application"),
            Op::If(_) => write!(f, "if"),
        }
    }
}

pub struct ExprParser<'p, 'i> {
    parser: &'p mut Parser<'i>,
    is_pat: bool,
    app_only: bool,
    term_last: bool,
    names: Vec<SName>,
    terms: Vec<Pre>,
    ops: Vec<Op<'i>>,
}
impl<'p, 'i> std::ops::Deref for ExprParser<'p, 'i> {
    type Target = Parser<'i>;

    fn deref(&self) -> &Self::Target {
        self.parser
    }
}
impl<'p, 'i> std::ops::DerefMut for ExprParser<'p, 'i> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.parser
    }
}
impl<'p, 'i: 'p> ExprParser<'p, 'i> {
    fn new(parser: &'p mut Parser<'i>, is_pat: bool) -> Self {
        ExprParser {
            parser,
            is_pat,
            app_only: false,
            term_last: false,
            names: Vec::new(),
            terms: Vec::new(),
            ops: Vec::new(),
        }
    }

    fn resolve_names(&mut self) -> PResult<()> {
        for name in self.names.split_off(0) {
            let term = Spanned::new(Pre_::Var(*name), name.span());
            self.push_term(term)?;
        }
        Ok(())
    }

    /// Helper function that takes two terms off the stack and combines them with the given operator
    fn resolve_op(&mut self, op: Op) -> PResult<()> {
        let b = self.terms.pop().ok_or_else(|| {
            self.err::<(), _>(format!("expected expression as operand to {}", op))
                .unwrap_err()
        })?;
        let a = self.terms.pop().ok_or_else(|| {
            self.err::<(), _>(format!("expected expression as operand to {}", op))
                .unwrap_err()
        })?;

        // Outer spans
        let vspan = Span(a.span().0, b.span().1);

        let v = match op {
            Op::App(icit) => Pre_::App(icit, a, b),
            Op::Tok(op) => {
                // Inner span
                let span = op.span();
                match *op {
                    Tok::And => Pre_::And(a, b),
                    Tok::Or => Pre_::Or(a, b),
                    // If we're resolving it already, we know it doesn't have a `with` clause
                    Tok::Arrow => Pre_::Fun(a, b, Vec::new()),
                    Tok::Plus => Pre_::BinOp(Spanned::new(BinOp::Add, span), a, b),
                    Tok::Minus => Pre_::BinOp(Spanned::new(BinOp::Sub, span), a, b),
                    Tok::Times => Pre_::BinOp(Spanned::new(BinOp::Mul, span), a, b),
                    Tok::Div => Pre_::BinOp(Spanned::new(BinOp::Div, span), a, b),
                    Tok::Mod => Pre_::BinOp(Spanned::new(BinOp::Mod, span), a, b),
                    Tok::Exp => Pre_::BinOp(Spanned::new(BinOp::Exp, span), a, b),
                    Tok::BitAnd => Pre_::BinOp(Spanned::new(BinOp::BitAnd, span), a, b),
                    Tok::Bar => Pre_::BinOp(Spanned::new(BinOp::BitOr, span), a, b),
                    Tok::Xor => Pre_::BinOp(Spanned::new(BinOp::BitXor, span), a, b),
                    Tok::LShift => Pre_::BinOp(Spanned::new(BinOp::BitShl, span), a, b),
                    Tok::RShift => Pre_::BinOp(Spanned::new(BinOp::BitShr, span), a, b),
                    Tok::Gt => Pre_::BinOp(Spanned::new(BinOp::Gt, span), a, b),
                    Tok::GtE => Pre_::BinOp(Spanned::new(BinOp::Geq, span), a, b),
                    Tok::Lt => Pre_::BinOp(Spanned::new(BinOp::Lt, span), a, b),
                    Tok::LtE => Pre_::BinOp(Spanned::new(BinOp::Leq, span), a, b),
                    Tok::Eq => Pre_::BinOp(Spanned::new(BinOp::Eq, span), a, b),
                    Tok::NEq => Pre_::BinOp(Spanned::new(BinOp::NEq, span), a, b),
                    Tok::Comma => todo!(","),
                    Tok::LPipe => todo!("pipes"),
                    Tok::RPipe => todo!("pipes"),
                    Tok::Else => {
                        // Resolve all remaining operators until we get to an `if`
                        self.resolve_names()?;
                        let mut ret = None;
                        while let Some(op2) = self.ops.pop() {
                            if let Op::If(cond) = op2 {
                                match cond {
                                    Some(cond) => {
                                        ret = Some(Pre_::If(cond, a, b));
                                        break;
                                    }
                                    None => return self.err("expected `then` in if expression"),
                                }
                            } else {
                                self.resolve_op(op2)?;
                            }
                        }
                        // No matching `if` on the stack, so give an error
                        match ret {
                            Some(v) => v,
                            None => return self.err("unexpected `else` without matching `if`"),
                        }
                    }
                    _ => panic!("Couldn't resolve {}", *op),
                }
            }
            Op::If(_) => unreachable!(),
        };
        self.terms.push(Spanned::new(v, vspan));
        Ok(())
    }

    fn resolve_for(&mut self, op: &Op<'p>) -> PResult<()> {
        self.resolve_names()?;
        let prec = op.binop_prec();

        // If we can, resolve the last operator
        while let Some(op2) = self.ops.last().cloned() {
            let prec2 = op2.binop_prec();
            if prec2 > prec || (prec2 == prec && op.associates_with(&op2)) {
                self.ops.pop().unwrap();
                self.resolve_op(op2)?;
            // Arrows are right associative, so resolve the last one first in stack order
            } else if prec2 < prec || (prec == Prec::Arrow && prec2 == Prec::Arrow) {
                break;
            } else {
                // TODO add span of other operator
                return self.err(format!(
                    "mixing {} and {} is ambiguous: try adding parentheses",
                    op, op2
                ));
            }
        }
        Ok(())
    }

    fn resolve_all(&mut self) -> PResult<()> {
        self.resolve_names()?;
        while let Some(op2) = self.ops.pop() {
            self.resolve_op(op2)?;
        }
        Ok(())
    }

    fn recurse(&mut self) -> PResult<Pre> {
        ExprParser::new(self.parser, self.is_pat).go()
    }

    fn app_next(&self) -> bool {
        self.term_last
    }

    fn push_term(&mut self, t: Pre) -> PResult<()> {
        if self.app_next() {
            // Application operator

            // If we can, resolve the last operator
            self.resolve_for(&Op::App(Icit::Expl))?;

            self.ops.push(Op::App(Icit::Expl));
        }
        self.terms.push(t);
        self.term_last = true;
        Ok(())
    }

    fn go(&mut self) -> PResult<Pre> {
        loop {
            match self.peek("expression") {
                Ok(Tok::Box) => {
                    if !self.terms.is_empty() {
                        return self.unexpected(Tok::Box, "expression");
                    } else {
                        let start = self.span().0;
                        self.next();
                        let x = self.recurse()?;
                        let span = Span(start, x.span().1);
                        return Ok(Spanned::new(Pre_::Box(true, x), span));
                    }
                }
                Ok(Tok::Unbox) => {
                    if !self.terms.is_empty() {
                        return self.unexpected(Tok::Unbox, "expression");
                    } else {
                        let start = self.span().0;
                        self.next();
                        let x = self.recurse()?;
                        let span = Span(start, x.span().1);
                        return Ok(Spanned::new(Pre_::Box(false, x), span));
                    }
                }
                Ok(Tok::Dot) => {
                    // Dot has the highest precedence, and is left associative, so no need to resolve any existing `op`s
                    if let Some(x) = self.names.pop() {
                        self.next();
                        let x = Spanned::new(Pre_::Var(*x), x.span());
                        let name = self.name()?;
                        let span = Span(x.span().0, name.span().1);

                        self.resolve_names()?;
                        self.push_term(Spanned::new(Pre_::Dot(x, name), span))?;
                    } else if let Some(x) = self.terms.pop() {
                        self.next();
                        let name = self.name()?;
                        let span = Span(x.span().0, name.span().1);

                        // No need for push_term, just put it back on the stack
                        self.terms.push(Spanned::new(Pre_::Dot(x, name), span));
                    } else {
                        return self.unexpected(Tok::Dot, "expression");
                    }
                }
                Ok(Tok::POpen) | Ok(Tok::SOpen) => {
                    let open_span = self.span();
                    let mut mode = ArgMode::PiOrLambda;
                    if !self.names.is_empty() || self.app_next() {
                        mode.not_pi();
                    }
                    let args = self
                        .names
                        .drain(..)
                        .map(|n| (n, Icit::Expl, None))
                        .collect();
                    match self.arg_group(&mut mode, args)? {
                        Ok(args) => {
                            let term = self.lambda_pi(args, mode)?;
                            self.push_term(term)?;
                        }
                        Err((args, icit, term)) => {
                            for (n, i, t) in args {
                                assert_eq!(i, Icit::Expl);
                                assert_eq!(t, None);
                                self.names.push(n);
                            }
                            self.resolve_names()?;
                            if icit == Icit::Impl {
                                // Can't be an op, must be an application
                                if !self.app_next() {
                                    return Err(Spanned::new(
                                        LexError::Other(
                                            "unexpected [, expected expression".to_string(),
                                        ),
                                        open_span,
                                    ));
                                }
                                self.resolve_for(&Op::App(Icit::Impl))?;
                                self.ops.push(Op::App(Icit::Impl));
                                self.terms.push(term);
                                self.term_last = true;
                            } else {
                                self.push_term(term)?;
                            }
                        }
                    }
                }
                Ok(Tok::WideArrow) if !self.is_pat => {
                    let args = self
                        .names
                        .drain(..)
                        .map(|n| (n, Icit::Expl, None))
                        .collect();
                    let term = self.lambda_pi(args, ArgMode::Lambda)?;
                    self.resolve_names()?;
                    self.push_term(term)?;
                }
                Ok(Tok::Name(_)) => {
                    let name = self.name()?;
                    self.names.push(name);
                }
                Ok(x) if x.starts_atom() => {
                    let x = self.atom()?;
                    self.resolve_names()?;
                    self.push_term(x)?;
                }
                Ok(x) if !self.app_only && x.binop_prec().is_some() => {
                    let op = Op::Tok(Spanned::new(x.clone(), self.span()));

                    // If we can, resolve the last operator
                    self.resolve_for(&op)?;

                    if !self.term_last {
                        return self.unexpected(x, "expression before operator")?;
                    }

                    self.next();

                    self.ops.push(op);
                    self.term_last = false;
                }
                Ok(Tok::With) if !self.app_only => {
                    // If we have any arrows on the stack, this goes with the top one; otherwise, we stop here
                    // So resolve all remaining operators until we get to an arrow
                    self.resolve_names()?;
                    let mut found = false;
                    while let Some(op2) = self.ops.pop() {
                        if op2.binop_prec() == Prec::Arrow {
                            let b = self.terms.pop().unwrap();
                            let a = self.terms.pop().ok_or_else(|| {
                                self.err::<(), _>(format!("expected return type after `->`"))
                                    .unwrap_err()
                            })?;
                            let span = Span(a.span().1, b.span().0);

                            // We haven't consumed the `with` yet, so we let `maybe_effs_list()` consume it
                            let effs = self.maybe_effs_list()?;

                            self.terms.push(Spanned::new(Pre_::Fun(a, b, effs), span));
                            found = true;
                            break;
                        } else {
                            self.resolve_op(op2)?;
                        }
                    }
                    // No matching arrow on the stack, so it belongs to an outer pi and we should stop
                    if !found {
                        break;
                    }
                }
                Ok(Tok::If) => {
                    self.resolve_names()?;
                    self.next();
                    self.ops.push(Op::If(None));
                    self.term_last = false;
                }
                Ok(Tok::Then) => {
                    // Resolve all remaining operators until we get to an `if`
                    self.resolve_names()?;
                    let mut found = false;
                    while let Some(op2) = self.ops.pop() {
                        if let Op::If(cond_slot) = op2 {
                            if cond_slot.is_some() {
                                return self.err("expected `else` branch before another `then`");
                            }
                            let cond = self.terms.pop();
                            if let Some(cond) = cond {
                                // Consume the `then`
                                self.next();

                                self.ops.push(Op::If(Some(cond)));
                                found = true;
                                self.term_last = false;
                                break;
                            } else {
                                return self.err("expected if condition before `then`");
                            }
                        } else {
                            self.resolve_op(op2)?;
                        }
                    }
                    // No matching `if` on the stack, so give an error
                    if !found {
                        return self.err("unexpected `then` without matching `if`");
                    }
                }
                Ok(Tok::Indent) if !self.app_only => {
                    self.next();

                    self.resolve_names()?;

                    let next = self.peek("expression").unwrap();
                    if next.binop_prec().is_some() {
                        // An operator starts the next line, so it has lower precedence than everything before
                        // So collapse all outstanding operators and go from there
                        self.resolve_all()?;
                        assert_eq!(self.terms.len(), 1);
                        loop {
                            match self.peek("expression")? {
                                Tok::Newline => {
                                    self.next();
                                    continue;
                                }
                                Tok::Dedent => {
                                    self.next();
                                    assert_eq!(self.terms.len(), 1);
                                    return Ok(self.terms.pop().unwrap());
                                }
                                x if x.binop_prec().is_some() => {
                                    let term = self.go()?;
                                    self.terms.push(term);
                                }
                                t => return self.unexpected(t, "expression")?,
                            }
                        }
                    } else if next == Tok::Then {
                        // Resolve all remaining operators until we get to an `if`
                        self.resolve_names()?;
                        let mut found = false;
                        while let Some(op2) = self.ops.pop() {
                            if let Op::If(cond_slot) = op2 {
                                if cond_slot.is_some() {
                                    return self
                                        .err("expected `else` branch before another `then`");
                                }
                                let cond = self.terms.pop().unwrap();

                                self.next();
                                self.ops.push(Op::If(Some(cond)));
                                found = true;
                                break;
                            } else {
                                self.resolve_op(op2)?;
                            }
                        }
                        // No matching `if` on the stack, so give an error
                        if !found {
                            return self.err("unexpected `then` without matching `if`");
                        } else {
                            let then_branch = self.recurse()?;
                            self.expect(Tok::Newline)?;
                            let op = self.expect(Tok::Else)?;
                            let else_branch = self.recurse()?;
                            self.expect(Tok::Dedent)?;
                            self.terms.push(then_branch);
                            self.terms.push(else_branch);
                            self.resolve_op(Op::Tok(op))?;
                        }
                    } else if self.app_next() {
                        // We're doing an application to the rest
                        self.resolve_for(&Op::App(Icit::Expl))?;
                        self.ops.push(Op::App(Icit::Expl));
                        let x = self.recurse()?;
                        self.terms.push(x);

                        while self.peek("") == Ok(Tok::Newline) {
                            self.next();
                            self.resolve_for(&Op::App(Icit::Expl))?;
                            self.ops.push(Op::App(Icit::Expl));
                            let x = self.recurse()?;
                            self.terms.push(x);
                        }

                        self.expect(Tok::Dedent)?;
                    } else {
                        // A normal operator applied to the rest
                        let x = self.recurse()?;
                        self.terms.push(x);
                        if self.peek("") == Ok(Tok::Newline) {
                            return self.err("expected end of expression and dedent");
                        }
                        self.expect(Tok::Dedent)?;
                    }
                }
                _ => break,
            }
        }

        // Resolve all remaining operators
        self.resolve_all()?;

        if self.terms.is_empty() {
            let tok = self.peek("expression")?;
            return self.unexpected(tok, "expression");
        }
        Ok(self.terms.pop().unwrap())
    }

    /// Parse either a lambda or a pi type, starting with the given arguments and the given possible modes.
    /// If `mode` is `PiOrLambda`, this function will disambiguate based on the arrow or the output of `arg_group()`.
    fn lambda_pi(
        &mut self,
        mut args: Vec<(SName, Icit, Option<PreTy>)>,
        mut mode: ArgMode,
    ) -> PResult<Pre> {
        self.args(&mut args, &mut mode, false)?;
        match self.peek("'=>' or '->'")? {
            Tok::Arrow => {
                if matches!(mode, ArgMode::PiOrLambda | ArgMode::Pi) {
                    self.next();

                    let body = self.term()?;

                    let effs = self.maybe_effs_list()?;

                    Ok(args
                        .into_iter()
                        .rfold((body, effs), |(to, effs), (name, icit, ty)| {
                            let ty = ty.unwrap_or_else(|| {
                                Spanned::new(Pre_::Hole(MetaSource::LocalType(*name)), name.span())
                            });
                            let span = Span(name.span().0, to.span().1);
                            (
                                Spanned::new(Pre_::Pi(*name, icit, ty, to, effs), span),
                                Vec::new(),
                            )
                        })
                        .0)
                } else {
                    self.err("pi type cannot have bare names as arguments")
                }
            }
            Tok::WideArrow => {
                self.next();

                let body = self.term()?;

                Ok(args.into_iter().rfold(body, |to, (name, icit, ty)| {
                    let ty = ty.unwrap_or_else(|| {
                        Spanned::new(Pre_::Hole(MetaSource::LocalType(*name)), name.span())
                    });
                    let span = Span(name.span().0, to.span().1);
                    Spanned::new(Pre_::Lam(*name, icit, ty, to), span)
                }))
            }

            t => self.unexpected(t, "'->' or '=>'"),
        }
    }

    /// Parse the arguments of a function-like structure, starting with the given arguments and the given possible modes.
    /// This function will add the arguments to `args`, and only change `mode` if `arg_group()` does.
    fn args(
        &mut self,
        args: &mut Vec<(SName, Icit, Option<PreTy>)>,
        mode: &mut ArgMode,
        indented: bool,
    ) -> PResult<()> {
        loop {
            if indented {
                self.maybe(Tok::Newline);
            }
            match self.peek(mode.str())? {
                Tok::Name(_) => {
                    let mut names = Vec::new();
                    while let Ok(Tok::Name(_)) = self.peek("_") {
                        names.push(self.name()?);
                    }

                    // If this is a constructor, then the bare words are actually individual type names.
                    if *mode == ArgMode::Cons {
                        args.extend(names.into_iter().map(|name| {
                            (
                                name.copy_span(self.db.intern_name("_".to_string())),
                                Icit::Expl,
                                Some(name.copy_span(Pre_::Var(*name))),
                            )
                        }));
                        continue;
                    }

                    // It's possible that these names aren't lambda arguments, but an application:
                    // the type of the last argument of a pi type. For example:
                    // `[t] Vec t 4 -> t`
                    // So, we only count them as bare names if the next token is one that can end an argument list.
                    let t = self.peek(mode.str())?;
                    if t.ends_args() && t != Tok::Arrow {
                        // They're bare names, so if it's a pi type that's an error
                        if !mode.not_pi() {
                            break self.err("pi type cannot have bare names as arguments");
                        }

                        args.extend(names.into_iter().map(|name| (name, Icit::Expl, None)));
                    } else {
                        // It's one application
                        if !mode.yes_pi() {
                            break self.unexpected(t, mode.str());
                        }

                        let mut term = ExprParser::new(self.parser, self.is_pat);
                        term.names = names;
                        term.app_only = true;
                        let term = term.go()?;
                        args.push((
                            term.copy_span(self.db.intern_name("_".to_string())),
                            Icit::Expl,
                            Some(term),
                        ));
                        // It must be the last argument
                        break Ok(());
                    }
                }
                Tok::POpen | Tok::SOpen => {
                    *args = self.arg_group(mode, args.take())?.unwrap();
                }

                t => {
                    if t.ends_args() {
                        break Ok(());
                    } else {
                        match mode {
                            ArgMode::Lambda | ArgMode::FunDef => {
                                break self.unexpected(t, mode.str())
                            }
                            ArgMode::Cons => {
                                let atom = self.atom()?;
                                args.push((
                                    atom.copy_span(self.db.intern_name("_".to_string())),
                                    Icit::Expl,
                                    Some(atom),
                                ));
                            }
                            ArgMode::Pi | ArgMode::PiOrLambda => {
                                mode.yes_pi();
                                let term = self.term()?;
                                args.push((
                                    term.copy_span(self.db.intern_name("_".to_string())),
                                    Icit::Expl,
                                    Some(term),
                                ));
                                break Ok(());
                            }
                        }
                    }
                }
            }
        }
    }

    /// Parse an argument group - the part inside the parentheses of `(a : _)`.
    ///
    /// If `mode` suggests that it may be a lambda, and this function sees something that's impossible for a lambda,
    /// it will resolve into a normal expression and return `Ok(Err(_))`.
    /// Otherwise, it will return the argument vector with new arguments added, wrapped in `Ok(Ok(_))`.
    ///
    /// This function may change `mode` if it sees something that is only valid for a subset of `mode`.
    fn arg_group(
        &mut self,
        mode: &mut ArgMode,
        mut args: Vec<(SName, Icit, Option<Pre>)>,
    ) -> PResult<
        Result<Vec<(SName, Icit, Option<Pre>)>, (Vec<(SName, Icit, Option<Pre>)>, Icit, Pre)>,
    > {
        let start = self.span().0;
        // Consume the ( or [
        let tok = self.next().unwrap();
        let (icit, closing) = match tok {
            Tok::POpen => (Icit::Expl, Tok::PClose),
            Tok::SOpen => (Icit::Impl, Tok::SClose),
            _ => panic!("Called arg_group() on token {}", tok),
        };

        match self.peek("_") {
            Ok(t) if t == closing => {
                let end = self.span().1;
                self.next();
                let span = Span(start, end);

                if matches!(mode, ArgMode::Lambda | ArgMode::PiOrLambda)
                    && !matches!(self.peek("_"), Ok(Tok::WideArrow) | Ok(Tok::Arrow) if !self.is_pat)
                {
                    let x = Spanned::new(Pre_::Unit, span);

                    return Ok(Err((args, icit, x)));
                } else {
                    args.push((
                        Spanned::new(self.db.intern_name("_".to_string()), span),
                        icit,
                        Some(Spanned::new(Pre_::Unit, span)),
                    ));
                }
            }

            // We've matched `a b (c`, so if the next character is `:` then it's a lambda, otherwise it isn't
            Ok(Tok::Name(_)) => {
                let mut names = Vec::new();
                while let Ok(Tok::Name(_)) = self.peek("_") {
                    names.push(self.name()?);
                }

                // If it's a lambda, we expect `(x: ty)`
                if let Ok(Tok::Colon) = self.peek("_") {
                    // Consume the :
                    self.next();
                    let ty = self.term()?;

                    self.expect(closing)?;

                    args.extend(names.into_iter().map(|name| (name, icit, Some(ty.clone()))));
                // If there's no colon, it can't be a lambda
                // Unless it's implicit and at the start of the argument list
                } else if *mode == ArgMode::Lambda
                    || (*mode == ArgMode::PiOrLambda && icit == Icit::Expl && args.is_empty())
                {
                    let mut in_parens = ExprParser::new(self.parser, false);
                    in_parens.names = names;
                    let in_parens = in_parens.go()?;

                    let end = self.span().1;
                    self.maybe(Tok::Newline);
                    self.expect(closing)?;

                    let span = Span(start, end);

                    // Untyped implicits `[x] => ...` can only appear at the front of lambdas, so they're not confused with passing an implicit argument
                    if icit == Icit::Impl && self.peek("_") == Ok(Tok::WideArrow) && !self.is_pat {
                        return Err(Spanned::new(
                            LexError::Other(
                                "implicit parameters with an inferred type are not allowed in lambdas; please add a colon `[x:]` instead"
                                .into()
                            ),
                            span,
                        ));
                    } else {
                        return Ok(Err((args, icit, in_parens.with_span(span))));
                    }
                } else if icit == Icit::Expl {
                    if mode.yes_pi() || *mode == ArgMode::Cons {
                        let mut term = ExprParser::new(self.parser, false);
                        term.names = names;
                        let term = term.go()?;

                        self.expect(closing)?;

                        args.push((
                            term.copy_span(self.db.intern_name("_".to_string())),
                            Icit::Expl,
                            Some(term),
                        ));
                        // TODO if this is a pi, this must be the last argument
                    } else {
                        return self
                            .err("expected ':' here: explicit parameter binding cannot omit type");
                    }
                } else {
                    self.expect(closing)?;

                    args.extend(names.into_iter().map(|name| (name, icit, None)));
                }
            }

            Ok(Tok::Colon) => {
                let cspan = self.span();
                let name = self.db.intern_name("_".to_string());
                // Consume the :
                self.next();

                let ty = self.term()?;

                self.expect(closing)?;

                args.push((Spanned::new(name, cspan), icit, Some(ty)));
            }

            t => {
                match mode {
                    ArgMode::Lambda | ArgMode::PiOrLambda
                        if *mode == ArgMode::Lambda || args.is_empty() =>
                    {
                        // It's actually an application
                        let in_parens = self.term()?;

                        self.maybe(Tok::Newline);
                        self.expect(closing)?;

                        return Ok(Err((args, icit, in_parens)));
                    }
                    ArgMode::FunDef => {
                        return match t {
                            Ok(t) => self.unexpected(t, mode.str()),
                            Err(e) => Err(e),
                        }
                    }
                    ArgMode::Cons => {
                        let term = self.term()?;
                        self.expect(closing)?;
                        args.push((
                            term.copy_span(self.db.intern_name("_".to_string())),
                            Icit::Expl,
                            Some(term),
                        ));
                    }
                    ArgMode::Pi | ArgMode::PiOrLambda => {
                        mode.yes_pi();
                        let term = self.term()?;
                        self.expect(closing)?;
                        args.push((
                            term.copy_span(self.db.intern_name("_".to_string())),
                            Icit::Expl,
                            Some(term),
                        ));
                        // TODO end pi type here
                    }
                    ArgMode::Lambda => unreachable!(),
                }
            }
        }

        Ok(Ok(args))
    }
}
