use super::{EffStack, MCxt};
use crate::common::*;
use crate::term::Lvl;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum ScopeType {
    Type(Name),
    Struct,
}

/// The reason we expected a value to have a given type, used in "could not match types" errors
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ReasonExpected {
    UsedAsType,
    UsedInWith,
    UsedInBox,
    IfCond,
    LogicOp,
    MustMatch(Span),
    Given(Span),
    ArgOf(Span, VTy),
}
impl ReasonExpected {
    pub fn span_or(&self, or: Span) -> Span {
        match self {
            ReasonExpected::MustMatch(s)
            | ReasonExpected::Given(s)
            | ReasonExpected::ArgOf(s, _) => *s,
            _ => or,
        }
    }

    /// Adds a description of the reason to the `err`.
    /// This function adds it to an existing error instead of returning a Doc because some reasons have spans attached, and some don't.
    pub fn add(self, err: Error, file: FileId, mcxt: &MCxt) -> Error {
        match self {
            ReasonExpected::UsedAsType => err
                .with_note(Doc::start("expected because it was used as a type").style(Style::Note)),
            ReasonExpected::UsedInWith => err.with_note(
                Doc::start("expected because it was used as an effect in a `with` type")
                    .style(Style::Note),
            ),
            ReasonExpected::UsedInBox => err.with_note(
                Doc::start("help: `box` and `unbox` can only be used with types")
                    .style(Style::Note),
            ),
            ReasonExpected::IfCond => err.with_note(
                Doc::start("expected because if conditions must have type Bool").style(Style::Note),
            ),
            ReasonExpected::LogicOp => err.with_note(
                Doc::start("expected because operands of `and` and `or` must have type Bool")
                    .style(Style::Note),
            ),
            ReasonExpected::MustMatch(span) => err.with_label(
                file,
                span,
                "expected because it must match the type of this",
            ),
            ReasonExpected::Given(span) => {
                err.with_label(file, span, "expected because it was given here")
            }
            ReasonExpected::ArgOf(span, ty) => err.with_label(
                file,
                span,
                Doc::start("expected because it was passed to this, of type")
                    .line()
                    .chain(ty.pretty(mcxt).style(Style::None))
                    .style(Style::Note),
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    NotFound(Spanned<Name>),
    NotFunction(Spanned<VTy>),
    Unify(Spanned<VTy>, VTy, ReasonExpected),
    NotIntType(Span, VTy, ReasonExpected),
    UntypedLiteral(Span),
    InvalidLiteral(Span, Literal, Builtin),
    MetaScope(Span, Var<Lvl>, Name),
    MetaOccurs(Span, Var<Lvl>),
    MetaSpine(Span, Var<Lvl>, Val),
    NotStruct(Spanned<VTy>),
    MemberNotFound(Span, ScopeType, Name),
    InvalidPattern(Span),
    WrongNumConsArgs(Span, usize, usize),
    Inexhaustive(Span, crate::pattern::Cov, VTy),
    InvalidPatternBecause(Box<TypeError>),
    WrongArity(Spanned<VTy>, usize, usize),
    EffNotAllowed(Span, Val, EffStack),
    /// No catchable effects for `catch` expression. If the `bool` is true, then IO was included.
    WrongCatchType(Span, bool),
    EffPatternType(Span, Span, Val, Vec<Val>),
    BinOpType(Span, VTy, Span),
    /// If the `bool` is true, this is a declaration outside a `sig`; otherwise, vice-versa.
    IllegalDec(Span, bool),
    /// An error has already been reported to the database, so this should be ignored.
    Sentinel,
}
impl TypeError {
    pub fn into_error(self, file: FileId, mcxt: &MCxt) -> Option<Error> {
        Some(match self {
            TypeError::Sentinel => return None,
            TypeError::IllegalDec(span, true) => Error::new(
                file,
                "Illegal declaration outside record signature",
                span,
                "declarations aren't allowed here; try adding a body with =",
            ),
            TypeError::IllegalDec(span, false) => Error::new(
                file,
                "Illegal non-declaration in record signature",
                span,
                "definitions aren't allowed here; try removing the body",
            ),
            TypeError::BinOpType(vspan, vty, opspan) => Error::new(
                file,
                Doc::start("Expected number in operand to binary operator, but got type ")
                    .chain(vty.pretty(mcxt).style(Style::None))
                    .style(Style::Bold),
                vspan,
                "expected number here"
            )
            .with_label(file, opspan, "in operand of this operator"),
            TypeError::NotFound(n) => Error::new(
                file,
                format!("Name not found in scope: '{}'", n.get(mcxt.db)),
                n.span(),
                "not found",
            ),
            TypeError::NotFunction(t) => Error::new(
                file,
                Doc::start("Expected function type in application, but got")
                    .line()
                    .chain(t.pretty(mcxt).style(Style::None))
                    .style(Style::Bold),
                t.span(),
                "not a function",
            ),
            TypeError::Unify(a, b, r) => r.add(
                Error::new(
                    file,
                    Doc::start("Could not match types, expected")
                        .line()
                        .chain(b.pretty(mcxt).style(Style::None))
                        .line()
                        .add("but got")
                        .line()
                        .chain(a.pretty(mcxt).style(Style::None))
                        .style(Style::Bold),
                    a.span(),
                    Doc::start("expected")
                        .line()
                        .chain(b.pretty(mcxt).style(Style::None))
                        .line()
                        .add("here")
                        .style(Style::Error),
                ),
                file,
                mcxt,
            ),
            // TODO do these two ever occur?
            TypeError::MetaScope(s, m, n) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt))
                    .add(" requires variable ")
                    .add(n.get(mcxt.db))
                    .add(", which is not in its scope")
                    .style(Style::Bold),
                s,
                "solution found here",
            ),
            TypeError::MetaOccurs(s, m) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt))
                    .add(" depends on itself")
                    .style(Style::Bold),
                s,
                "solution found here",
            ),
            // TODO: this is complicated to explain, so make and link to a wiki page in the error message
            TypeError::MetaSpine(s, m, v) => Error::new(
                file,
                Doc::start("Solution for ")
                    .chain(m.pretty_meta(mcxt))
                    .add(" is ambiguous: cannot depend on value")
                    .line()
                    .chain(v.pretty(mcxt).style(Style::None))
                    .style(Style::Bold),
                s,
                "solution depends on a non-variable",
            )
            .with_note(Doc::start("because here it depends on a specific value, the compiler doesn't know what the solution should be for other values").style(Style::Note)),
            TypeError::NotStruct(ty) => Error::new(
                file,
                Doc::start("Value of type")
                    .line()
                    .chain(ty.pretty(mcxt).style(Style::None))
                    .line()
                    .add("does not have members")
                    .style(Style::Bold),
                ty.span(),
                "tried to access member here",
            ),
            TypeError::MemberNotFound(span, sctype, m) => Error::new(
                file,
                Doc::start("Could not find member ")
                    .add(mcxt.db.lookup_intern_name(m))
                    .add(" in ")
                    .add(match sctype {
                        ScopeType::Type(name) => {
                            format!("namespace of type {}", mcxt.db.lookup_intern_name(name))
                        }
                        ScopeType::Struct => "struct".to_string(),
                    })
                    .style(Style::Bold),
                span,
                format!("not found: {}", mcxt.db.lookup_intern_name(m)),
            ),
            TypeError::InvalidPattern(span) => Error::new(
                file,
                Doc::start("Invalid pattern: expected '_', variable, literal, or constructor")
                    .style(Style::Bold),
                span,
                "invalid pattern",
            ),
            TypeError::WrongNumConsArgs(span, expected, got) => Error::new(
                file,
                Doc::start("Expected ")
                    .add(expected)
                    .add(" arguments to constructor in pattern, got ")
                    .add(got)
                    .style(Style::Bold),
                span,
                format!("expected {} arguments", expected),
            ),
            TypeError::Inexhaustive(span, cov, ty) => Error::new(
                file,
                Doc::start("Inexhaustive match: patterns")
                    .line()
                    .chain(cov.pretty_rest(&ty, mcxt).style(Style::None))
                    .line()
                    .add("not covered")
                    .style(Style::Bold),
                span,
                Doc::start("this has type ")
                    .chain(ty.pretty(mcxt).style(Style::None))
                    .style(Style::Error),
            ),
            TypeError::InvalidPatternBecause(e) => {
                let mut e = e.into_error(file, mcxt)?;
                let message = format!("Invalid pattern: {}", e.message());
                *e.message() = message;
                e
            }
            TypeError::NotIntType(span, ty, r) => r.add(
                Error::new(
                    file,
                    Doc::start("Expected value of type")
                        .line()
                        .chain(ty.pretty(mcxt).style(Style::None))
                        .line()
                        .add("but got integer")
                        .style(Style::Bold),
                    span,
                    "this is an integer",
                ),
                file,
                mcxt,
            ),
            TypeError::UntypedLiteral(span) => Error::new(
                file,
                Doc::start("Could not infer type of ambiguous literal").style(Style::Bold),
                span,
                Doc::start("try adding a type, like ")
                    .chain(Doc::start("I32").style(Style::None))
                    .add(" or ")
                    .chain(Doc::start("I64").style(Style::None))
                    .style(Style::Error),
            ),
            TypeError::InvalidLiteral(span, l, t) => Error::new(
                file,
                Doc::start("Invalid literal for type ")
                    .add(t.name())
                    .add(": value ")
                    .chain(l.pretty(mcxt.db)),
                span,
                Doc::start("Does not fit in type ")
                    .add(t.name()),
            ),
            TypeError::EffNotAllowed(span, eff, mut stack) => {
                let base = Error::new(
                    file,
                    Doc::start("Effect")
                        .line()
                        .chain(eff.pretty(mcxt).style(Style::None))
                        .line()
                        .add("not allowed in this context")
                        .style(Style::Bold),
                    span,
                    Doc::start("this performs effect")
                        .line()
                        .chain(eff.pretty(mcxt).style(Style::None))
                        .style(Style::Error)
                );
                if stack.scopes.is_empty() {
                    base.with_note("effects are not allowed in the top level context")
                } else if stack.scope_start().unwrap() == stack.effs.len() {
                    base.with_label(file, stack.scopes.last().unwrap().2, "this context does not allow effects")
                } else {
                    base.with_label(file, stack.scopes.last().unwrap().2,
                        Doc::start("this context allows effects ")
                            .chain(Doc::intersperse(stack.pop_scope().into_iter().map(|eff| eff.pretty(mcxt).style(Style::None)), Doc::start(",").space()))
                            .style(Style::Error)
                    )
                }
            }
            TypeError::WrongArity(ty, expected, got) => Error::new(
                file,
                Doc::start(if got > expected {
                    "Too many arguments "
                } else {
                    "Too few arguments "
                })
                .add(got)
                .add(" to value of type")
                .line()
                .chain(ty.pretty(mcxt).style(Style::None))
                .line()
                .add("which expects ")
                .add(expected)
                .add(if expected == 1 {
                    " argument"
                } else {
                    " arguments"
                })
                .style(Style::Bold),
                ty.span(),
                format!(
                    "expected {} {} here, got {}",
                    expected,
                    if expected == 1 {
                        "argument"
                    } else {
                        "arguments"
                    },
                    got
                ),
            ),
            TypeError::WrongCatchType(span, has_io) => Error::new(
                file,
                Doc::start("`catch` expression requires effect to catch, but expression performs no catchable effects")
                    .style(Style::Bold),
                span,
                if has_io {
                    "this expression only performs the IO effect, which can't be caught"
                } else {
                    "this expression performs no effects"
                },
            )
            .with_note(
                Doc::start("to pattern-match on a value without effects, use ")
                    .chain(Doc::keyword("case"))
                    .add(" instead of ")
                    .chain(Doc::keyword("catch"))
                    .style(Style::Note)
            ),
            TypeError::EffPatternType(vspan, pspan, _ty, effs) if effs.is_empty() => Error::new(
                file,
                Doc::start("`eff` pattern requires caught effects to match against, but `case` doesn't catch effects")
                    .style(Style::Bold),
                pspan,
                "`eff` pattern requires effects",
            )
            .with_label(
                file,
                vspan,
                Doc::start("if this expression performs effects, try using ")
                    .chain(Doc::keyword("catch"))
                    .add(" instead of ")
                    .chain(Doc::keyword("case"))
                    .add(" here")
                    .style(Style::Note),
            ),
            TypeError::EffPatternType(vspan, pspan, ty, effs) => Error::new(
                file,
                Doc::start("got effect type")
                    .line()
                    .chain(ty.pretty(mcxt).style(Style::None))
                    .line()
                    .add("but expected one of")
                    .line()
                    .chain(Doc::intersperse(effs.iter().map(|e| e.pretty(mcxt).style(Style::None)), Doc::start(',').space()))
                    .style(Style::Bold),
                pspan,
                "wrong effect type for `eff` pattern",
            )
            .with_label(
                file,
                vspan,
                Doc::start("this expression performs effects")
                    .line()
                    .chain(Doc::intersperse(effs.iter().map(|e| e.pretty(mcxt).style(Style::None)), Doc::start(',').line()).group())
                    .style(Style::Note),
            ),
        })
    }
}
