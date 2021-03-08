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
        match self.buf {
            Some(t) => Some(t),
            None => {
                match self.lexer.next() {
                    Some(Ok(t)) => self.buf = Some(t),
                    Some(Err(e)) => self.pending_err = Some(e),
                    None => (),
                }
                self.buf
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

    fn err<T>(&mut self, msg: impl Into<String>) -> PResult<T> {
        let span = self.lexer.span();
        PResult::Err(Spanned::new(LexError::Other(msg.into()), span))
    }

    fn unexpected<T>(&mut self, tok: Tok<'i>, expected: &str) -> PResult<T> {
        self.err(format!("unexpected {}, expected {}", tok, expected))
    }
}

/// Parsing
impl<'i> Parser<'i> {
    /// Parse top-level definitions until the end of the input.
    pub fn defs(&mut self) -> PResult<Vec<PreDefAn>> {
        let mut v = Vec::new();
        let mut had_newline = true;
        self.newline();
        while self.has_next() {
            if !had_newline {
                let next_tok = self.peek("_")?;
                return self.unexpected(next_tok, "newline before next definition");
            }
            v.push(self.def()?);
            had_newline = self.newline();
        }
        Ok(v)
    }

    /// Consume one or more newlines or semicolons, returning whether any were consumed.
    fn newline(&mut self) -> bool {
        let mut ret = false;
        while self.has_next() {
            match self.peek("newline").unwrap() {
                Tok::Newline => {
                    self.next();
                    ret = true;
                }
                _ => break,
            }
        }
        ret
    }

    /// Consume a token, and give an error if it doesn't match the provided token.
    fn expect(&mut self, tok: Tok<'i>) -> PResult<()> {
        let t = self.next();
        if t != Some(tok) {
            if let Some(ty) = tok.closes_type() {
                Err(Spanned::new(LexError::MissingTerminator(ty), self.span()))
            } else if let Some(t) = t {
                self.unexpected(t, &format!("{}", tok))
            } else {
                self.err(format!("unexpected end of input, expected {}", tok))
            }
        } else {
            Ok(())
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

                self.newline();

                let mut def = self.def()?;
                def.attributes.push(attr);
                Ok(def)
            }
            Tok::Val => {
                // Consume the `val`
                self.next();
                self.newline();

                let name = self.name()?;

                let ty = if let Tok::Colon = self.peek("=")? {
                    // Consume the :
                    self.next();

                    self.term()?
                } else {
                    Spanned::new(Pre_::Hole(MetaSource::LocalType(*name)), name.span())
                };

                match self.peek("=")? {
                    Tok::Equals => {
                        self.next();
                    }
                    t => return self.unexpected(t, "="),
                }

                let body = self.term()?;

                Ok(PreDef::Val(name, ty, body).into())
            }
            Tok::Fun => {
                // Consume the `fun`
                self.next();

                let name = self.name()?;

                let mut args = Vec::new();
                self.args(&mut args, &mut ArgMode::FunDef)?;
                let args = args
                    .into_iter()
                    .map(|(n, i, t)| {
                        let t =
                            t.unwrap_or_else(|| n.copy_span(Pre_::Hole(MetaSource::LocalType(*n))));
                        (*n, i, t)
                    })
                    .collect();

                let ty = if let Tok::Colon = self.peek("=")? {
                    // Consume the :
                    self.next();

                    self.term()?
                } else {
                    Spanned::new(Pre_::Hole(MetaSource::LocalType(*name)), name.span())
                };

                let effs = self.maybe_effs_list()?;

                self.expect(Tok::Equals)?;

                let body = self.term()?;

                // TODO: do we ever infer effects? Maybe if no return type is given?
                Ok(PreDef::Fun(name, args, ty, body, Some(effs)).into())
            }
            Tok::Type | Tok::Eff => {
                // Consume the `type` or `eff`
                let is_eff = match self.next().unwrap() {
                    Tok::Type => false,
                    Tok::Eff => true,
                    _ => unreachable!(),
                };

                let name = self.name()?;

                let mut args = Vec::new();
                self.args(&mut args, &mut ArgMode::FunDef)?;
                let args: Vec<_> = args
                    .into_iter()
                    .map(|(n, i, t)| {
                        let t =
                            t.unwrap_or_else(|| n.copy_span(Pre_::Hole(MetaSource::LocalType(*n))));
                        (*n, i, t)
                    })
                    .collect();

                self.expect(Tok::Of)?;
                self.newline();

                // Now the constructors
                let mut ctors = Vec::new();
                let mut had_newline = true;
                while !matches!(self.peek("_"), Err(_) | Ok(Tok::End) | Ok(Tok::Where)) {
                    if !had_newline {
                        let next_tok = self.peek("_")?;
                        return self.unexpected(next_tok, "newline before next definition");
                    }

                    let name = self.name()?;

                    let mut args = Vec::new();
                    self.args(&mut args, &mut ArgMode::Cons)?;
                    let args: Vec<_> = args
                        .into_iter()
                        .map(|(n, i, t)| {
                            let t = t.unwrap_or_else(|| {
                                n.copy_span(Pre_::Hole(MetaSource::LocalType(*n)))
                            });
                            (*n, i, t)
                        })
                        .collect();

                    let ty = if self.peek("_") == Ok(Tok::Colon) {
                        // Consume the :
                        self.next();

                        Some(self.term()?)
                    } else {
                        None
                    };

                    ctors.push(PreCons(name, args, ty));
                    had_newline = self.newline();
                }

                // Do the associated namespace
                let mut assoc = Vec::new();
                if self.peek("'end' or 'where'")? == Tok::Where {
                    self.next();
                    self.newline();
                    let mut had_newline = true;

                    while !matches!(self.peek("_"), Err(_) | Ok(Tok::End)) {
                        if !had_newline {
                            let next_tok = self.peek("_")?;
                            return self.unexpected(next_tok, "newline before next definition");
                        }
                        assoc.push(self.def()?);
                        had_newline = self.newline();
                    }
                }

                self.expect(Tok::End)?;

                Ok(PreDef::Type(name, is_eff, args, ctors, assoc).into())
            }
            _ => {
                // We don't allow lambdas in expression statements, so the multiline lambda syntax is ambiguous
                let term = self.binop(Vec::new())?;
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
        // Four possibilities:
        // 1. a lambda, starting with a name, `(x:`, `(:`, or `[x`
        // 2. a pi type, starting with `(x:`, `(:`, or `[x`
        // 3. an expression starting with a variable, like `f x y` or `a + b`, or a paren, like `(a + b) * c`
        // 4. anything else
        match self.peek("expression")? {
            Tok::Name(_) => {
                // It's either a normal expression starting with a variable, or a lambda
                // We can't tell until we see something other than a name
                let mut names = Vec::new();
                while let Ok(Tok::Name(_)) = self.peek("_") {
                    names.push(self.name()?);
                }

                self.lambda_app(names)
            }

            // If it starts with `(`, it could still be any of those things.
            // What's inside the parentheses will disambiguate it, so we'll let `arg_group()` handle that.
            Tok::POpen => {
                let mut mode = ArgMode::PiOrLambda;
                match self.arg_group(&mut mode, Vec::new())? {
                    Ok(args) => self.lambda_pi(args, mode),
                    Err(val) => Ok(val),
                }
            }

            // If it starts with `[`, it's either a lambda or a pi type
            Tok::SOpen => self.lambda_pi(Vec::new(), ArgMode::PiOrLambda),

            _ => self.binop(Vec::new()),
        }
    }

    /// After having seen one or more bare names, parse either a lambda or another expression that starts with an application.
    /// It will be disambiguated by `arg_group()`, or by seeing `=>` or a token not allowed in lambda parameters.
    fn lambda_app(&mut self, mut names: Vec<SName>) -> PResult<Pre> {
        // It's either a normal expression starting with a variable, or a lambda
        // We can't tell until we see something other than a name
        while let Ok(Tok::Name(_)) = self.peek("_") {
            names.push(self.name()?);
        }

        // If it's a lambda, we'll have either `=>`, `(x:`, or `[x:` next
        match self.peek("_") {
            Ok(Tok::POpen) | Ok(Tok::SOpen) => {
                let mut mode = ArgMode::Lambda;
                let args = names.into_iter().map(|n| (n, Icit::Expl, None)).collect();
                match self.arg_group(&mut mode, args)? {
                    Ok(args) => self.lambda_pi(args, mode),
                    Err(val) => Ok(val),
                }
            }

            // If we see `=>`, it's definitely a lambda
            Ok(Tok::WideArrow) => self.lambda_pi(
                names.into_iter().map(|n| (n, Icit::Expl, None)).collect(),
                ArgMode::Lambda,
            ),

            // It's not one of those three things, so it must be another expression
            // We actually need to special case dot as well, since app2 doesn't handle it
            Ok(Tok::Dot) if names.len() == 1 => {
                let f = to_term(names).unwrap();
                self.next();

                let name = match self.peek("member name")? {
                    Tok::Name(n) => Spanned::new(self.db.intern_name(n.to_string()), self.span()),
                    t => return self.unexpected(t, "member name"),
                };
                self.next();

                let args = self.app_args()?;
                let span = Span(
                    f.span().0,
                    args.last().map_or(name.span().1, |(_, x)| x.span().1),
                );
                Ok(Spanned::new(Pre_::Dot(f, name, args), span))
            }
            _ => {
                let term = to_term(names).unwrap();
                let term = self.app2(term)?;

                let terms = vec![term];
                self.binop(terms)
            }
        }
    }

    /// Parse either a lambda or a pi type, starting with the given arguments and the given possible modes.
    /// If `mode` is `PiOrLambda`, this function will disambiguate based on the arrow or the output of `arg_group()`.
    fn lambda_pi(
        &mut self,
        mut args: Vec<(SName, Icit, Option<PreTy>)>,
        mut mode: ArgMode,
    ) -> PResult<Pre> {
        self.args(&mut args, &mut mode)?;
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
    ) -> PResult<()> {
        loop {
            // Newlines between argument groups aren't ambiguous since we'll see when the arguments end.
            // *Unless* this is a constructor, in which case a newline ends the arguments.
            if *mode != ArgMode::Cons {
                self.newline();
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

                        let term = to_term(names).unwrap();
                        let term = self.app2(term)?;
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

    /// A helper function for `arg_group`, which assumes that the arguments so far were actually atoms in an application,
    /// and resolves them into an application, then applies `x` with icit `icit`.
    fn resolve_group_as_app(
        &mut self,
        args: Vec<(SName, Icit, Option<Pre>)>,
        icit: Icit,
        x: Pre,
    ) -> PResult<Pre> {
        if let Some(term) = args.into_iter().fold(None, |f, (name, icit, t)| {
            if t.is_some() {
                return Some(
                    self.err("unexpected application argument, expected lambda parameter"),
                );
            }
            let x = Spanned::new(Pre_::Var(*name), name.span());
            match f {
                None => Some(Ok(x)),
                Some(Ok(f)) => {
                    let span = Span(f.span().0, x.span().1);
                    Some(Ok(Spanned::new(Pre_::App(icit, f, x), span)))
                }
                Some(Err(e)) => Some(Err(e)),
            }
        }) {
            let term = term?;
            let span = Span(term.span().0, x.span().1);
            let term = Spanned::new(Pre_::App(icit, term, x), span);
            let term = self.app2(term)?;

            let terms = vec![term];
            self.binop(terms)
        } else {
            let term = self.app2(x)?;

            let terms = vec![term];
            self.binop(terms)
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
    ) -> PResult<Result<Vec<(SName, Icit, Option<Pre>)>, Pre>> {
        let start = self.span().0;
        // Consume the ( or [
        let tok = self.next().unwrap();
        let (icit, closing) = match tok {
            Tok::POpen => (Icit::Expl, Tok::PClose),
            Tok::SOpen => (Icit::Impl, Tok::SClose),
            _ => panic!("Called arg_gruop() on token {}", tok),
        };

        match self.peek("_") {
            Ok(t) if t == closing => {
                let end = self.span().1;
                self.next();
                let span = Span(start, end);

                if matches!(mode, ArgMode::Lambda | ArgMode::PiOrLambda)
                    && !matches!(self.peek("_"), Ok(Tok::WideArrow) | Ok(Tok::Arrow))
                {
                    let x = Spanned::new(Pre_::Unit, span);

                    return self.resolve_group_as_app(args, icit, x).map(Err);
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
                } else if (*mode == ArgMode::Lambda && (icit == Icit::Expl || !args.is_empty()))
                    || (matches!(mode, ArgMode::Lambda | ArgMode::PiOrLambda)
                        && icit == Icit::Expl
                        && args.is_empty())
                {
                    let in_parens = self.lambda_app(names)?;
                    let in_parens = self.binop(vec![in_parens])?;

                    let end = self.span().1;
                    self.expect(closing)?;

                    let ret = self.resolve_group_as_app(args, icit, in_parens).map(Err);

                    // Untyped implicits `[x] => ...` can only appear at the front of lambdas, so they're not confused with passing an implicit argument
                    if icit == Icit::Impl && self.peek("_") == Ok(Tok::WideArrow) {
                        let span = Span(start, end);
                        return Err(Spanned::new(
                            LexError::Other(
                                "implicit parameters with an inferred type can only appear at the front of lambdas; try using a type hole `[x : _]` instead"
                                .into()
                            ),
                            span,
                        ));
                    } else {
                        return ret;
                    }
                } else if icit == Icit::Expl {
                    if mode.yes_pi() {
                        let term = to_term(names).unwrap();
                        let term = self.app2(term)?;
                        let term = self.binop(vec![term])?;

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

                        self.expect(closing)?;

                        return self.resolve_group_as_app(args, icit, in_parens).map(Err);
                    }
                    ArgMode::FunDef => {
                        return match t {
                            Ok(t) => self.unexpected(t, mode.str()),
                            Err(e) => Err(e),
                        }
                    }
                    ArgMode::Cons => {
                        let atom = self.atom()?;
                        self.expect(closing)?;
                        args.push((
                            atom.copy_span(self.db.intern_name("_".to_string())),
                            Icit::Expl,
                            Some(atom),
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

    /// Parse an expression consisting of applications and binary operators, with a form of the shunting-yard algorithm.
    /// This can parse any Pika expression except lambdas and pi types.
    fn binop(&mut self, mut terms: Vec<Pre>) -> PResult<Pre> {
        // The shunting-yard algorithm
        // Except, we don't handle parentheses here - we call `app()` for operands,
        // and that handles paretheses and calls `binop()` recursively.
        let mut ops: Vec<Tok<'i>> = Vec::new();

        /// Helper function that takes two terms off the stack and combines them with the given operator
        fn resolve_op(terms: &mut Vec<Pre>, op: Tok) {
            let b = terms.pop().unwrap();
            let a = terms.pop().unwrap();

            // Inner and outer spans
            let span = Span(a.span().1, b.span().0);
            let vspan = Span(a.span().0, b.span().1);

            let v = match op {
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
                _ => panic!("Couldn't resolve {}", op),
            };
            terms.push(Spanned::new(v, vspan));
        }

        // Get ready for an operator next
        if terms.len() % 2 == 0 {
            terms.push(self.app()?);
        }

        while self.has_next() {
            let op = self.peek("_").unwrap();
            if let Some(prec) = op.binop_prec() {
                // If we can, resolve the last operator
                while let Some(op2) = ops.last().cloned() {
                    let prec2 = op2.binop_prec().unwrap();
                    if prec2 > prec || (prec2 == prec && op.associates_with(op2)) {
                        ops.pop().unwrap();
                        resolve_op(&mut terms, op2);
                    // Arrows are right associative, so resolve the last one first in stack order
                    } else if prec2 < prec || (prec == Prec::Arrow && prec2 == Prec::Arrow) {
                        break;
                    } else {
                        // TODO add span of other operator
                        return self.err(format!(
                            "mixing operators {} and {} is ambiguous: try adding parentheses",
                            op, op2
                        ));
                    }
                }

                // Push the operator and the next operand onto the stack
                self.next();
                ops.push(op);

                terms.push(self.app()?);
            } else {
                match op {
                    Tok::With => {
                        // If we have any arrows on the stack, this goes with the top one; otherwise, we stop here
                        // So resolve all remaining operators until we get to an arrow
                        let mut found = false;
                        while let Some(op2) = ops.pop() {
                            if let Tok::Arrow = op2 {
                                let b = terms.pop().unwrap();
                                let a = terms.pop().unwrap();
                                let span = Span(a.span().1, b.span().0);

                                // We haven't consumed the `with` yet, so we let `maybe_effs_list()` consume it
                                let effs = self.maybe_effs_list()?;

                                terms.push(Spanned::new(Pre_::Fun(a, b, effs), span));
                                found = true;
                                break;
                            } else {
                                resolve_op(&mut terms, op2);
                            }
                        }
                        // No matching arrow on the stack, so it belongs to an outer pi and we should stop
                        if !found {
                            break;
                        }
                    }
                    Tok::OpNewline => {
                        // A newline before a binop essentially wraps the previous lines in parentheses
                        self.next();
                        // Resolve all remaining operators
                        while let Some(op2) = ops.pop() {
                            resolve_op(&mut terms, op2);
                        }
                        // And if the next token is a dot, do that first
                        if let Ok(Tok::Dot) = self.peek("_") {
                            self.next();

                            let f = terms.pop().unwrap();

                            let name = match self.peek("member name")? {
                                Tok::Name(n) => {
                                    Spanned::new(self.db.intern_name(n.to_string()), self.span())
                                }
                                t => return self.unexpected(t, "member name"),
                            };
                            self.next();

                            let args = self.app_args()?;
                            let span = Span(
                                f.span().0,
                                args.last().map_or(name.span().1, |(_, x)| x.span().1),
                            );
                            terms.push(Spanned::new(Pre_::Dot(f, name, args), span))
                        }
                    }
                    _ => break,
                }
            }
        }

        // Resolve all remaining operators
        while let Some(op2) = ops.pop() {
            resolve_op(&mut terms, op2);
        }

        assert_eq!(terms.len(), 1);
        Ok(terms.pop().unwrap())
    }

    /// Parse an application, of the form `a`, `a b c`, `a.n`, or `a.n b c`, where `a b c` are atoms and `n` is a name.
    fn app(&mut self) -> PResult<Pre> {
        let f = self.atom()?;
        if let Ok(Tok::Dot) = self.peek("_") {
            self.next();

            let name = match self.peek("member name")? {
                Tok::Name(n) => Spanned::new(self.db.intern_name(n.to_string()), self.span()),
                t => return self.unexpected(t, "member name"),
            };
            self.next();

            let args = self.app_args()?;
            let span = Span(
                f.span().0,
                args.last().map_or(name.span().1, |(_, x)| x.span().1),
            );
            Ok(Spanned::new(Pre_::Dot(f, name, args), span))
        } else {
            self.app2(f)
        }
    }

    /// Parse an application, starting with the given term and collecting any arguments passed to it.
    /// This doesn't consider the `a.b` case like `app()` does, since the term passed to `app2()` may itself be an application.
    fn app2(&mut self, mut f: Pre) -> PResult<Pre> {
        loop {
            match self.peek("_") {
                Ok(Tok::Name(_)) | Ok(Tok::Lit(_)) | Ok(Tok::POpen) | Ok(Tok::Struct)
                | Ok(Tok::Sig) | Ok(Tok::TypeType) | Ok(Tok::Case) | Ok(Tok::Catch)
                | Ok(Tok::COpen) | Ok(Tok::Do) | Ok(Tok::If) => {
                    let x = self.atom()?;
                    let span = Span(f.span().0, x.span().1);
                    f = Spanned::new(Pre_::App(Icit::Expl, f, x), span);
                }
                Ok(Tok::SOpen) => {
                    self.next();

                    let x = self.term()?;

                    self.expect(Tok::SClose)?;

                    let span = Span(f.span().0, x.span().1);
                    f = Spanned::new(Pre_::App(Icit::Impl, f, x), span);
                }
                _ => break Ok(f),
            }
        }
    }

    /// Parse only the arguments of an application, as a vector; only used in parsing expressions fo the form `a.n b c`.
    fn app_args(&mut self) -> PResult<Vec<(Icit, Pre)>> {
        let mut v = Vec::new();
        loop {
            match self.peek("_") {
                Ok(Tok::Name(_)) | Ok(Tok::Lit(_)) | Ok(Tok::POpen) | Ok(Tok::Struct)
                | Ok(Tok::Sig) | Ok(Tok::TypeType) | Ok(Tok::Case) | Ok(Tok::Catch)
                | Ok(Tok::COpen) | Ok(Tok::Do) | Ok(Tok::If) => {
                    let x = self.atom()?;
                    v.push((Icit::Expl, x));
                }
                Ok(Tok::SOpen) => {
                    self.next();

                    let x = self.term()?;

                    self.expect(Tok::SClose)?;

                    v.push((Icit::Impl, x));
                }
                _ => break Ok(v),
            }
        }
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

                self.expect(Tok::PClose)?;

                Ok(ret)
            }
            Tok::Name(_) => {
                let name = self.name()?;
                Ok(Spanned::new(Pre_::Var(*name), name.span()))
            }
            Tok::Lit(l) => {
                self.next();
                Ok(Spanned::new(Pre_::Lit(l), self.span()))
            }
            Tok::TypeType => {
                self.next();
                Ok(Spanned::new(Pre_::Type, self.span()))
            }
            Tok::Do => {
                let start = self.span().0;
                self.next();
                self.newline();

                let mut v = Vec::new();
                let mut had_newline = true;

                while self.has_next() && self.peek("_") != Ok(Tok::End) {
                    if !had_newline {
                        let next_tok = self.peek("_")?;
                        return self.unexpected(next_tok, "newline before next definition");
                    }
                    v.push(self.def()?);
                    had_newline = self.newline();
                }

                let end = self.span().1;
                self.expect(Tok::End)?;

                Ok(Spanned::new(Pre_::Do(v), Span(start, end)))
            }
            Tok::If => {
                let start = self.span().0;
                self.next();
                self.newline();

                let cond = self.term()?;
                self.newline();

                self.expect(Tok::Then)?;
                self.newline();

                let yes = self.term()?;
                self.newline();

                self.expect(Tok::Else)?;
                self.newline();

                let no = self.term()?;
                let end = no.span().1;

                Ok(Spanned::new(Pre_::If(cond, yes, no), Span(start, end)))
            }
            Tok::Case | Tok::Catch => {
                let start = self.span().0;
                let is_catch = match self.next().unwrap() {
                    Tok::Case => false,
                    Tok::Catch => true,
                    _ => unreachable!(),
                };
                self.newline();

                let scrutinee = self.term()?;
                self.newline();

                self.expect(Tok::Of)?;
                self.newline();

                let mut v = Vec::new();
                let mut had_newline = true;

                while self.has_next() && self.peek("_") != Ok(Tok::End) {
                    if !had_newline {
                        let next_tok = self.peek("_")?;
                        return self.unexpected(next_tok, "newline before next case branch");
                    }

                    let pat = self.pat()?;
                    self.expect(Tok::WideArrow)?;
                    let body = self.term()?;

                    v.push((pat, body));

                    had_newline = self.newline();
                }

                let end = self.span().1;
                self.expect(Tok::End)?;

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
            _ => self.binop(Vec::new()),
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

fn to_term(names: Vec<SName>) -> Option<Pre> {
    names.into_iter().fold(None, |f, name| {
        let x = Spanned::new(Pre_::Var(*name), name.span());
        match f {
            None => Some(x),
            Some(f) => {
                let span = Span(f.span().0, x.span().1);
                Some(Spanned::new(Pre_::App(Icit::Expl, f, x), span))
            }
        }
    })
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
    fn ends_args(self) -> bool {
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
                | Tok::End
                | Tok::With
        )
    }

    /// Whether this token and another token can be used together left-associatively in expressions like `a + b - c`.
    /// Arithmetic operators return `true` if `other` has the same precedence; otherwise, most return `false`.
    fn associates_with(self, other: Tok<'i>) -> bool {
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
    fn binop_prec(self) -> Option<Prec> {
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
            _ => return None,
        })
    }
}
