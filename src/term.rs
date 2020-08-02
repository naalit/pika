use crate::common::*;
use crate::elab::Elab;
use crate::error::Spanned;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Def(pub Spanned<Sym>, pub STerm);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement {
    Expr(STerm),
    Def(Def),
}

/// A spanned term. Most terms will have this type
pub type STerm = Spanned<Term>;

/// A `Term` represents a type or term `before` reduction.
/// We do type checking on `Term`s, and when we want to use it as a type we `reduce()` it to a `Value`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Unit,                                         // ()
    The(STerm, STerm),                            // the T x
    Binder(Sym, Option<STerm>),                   // x: T
    Var(Sym),                                     // a
    I32(i32),                                     // 3
    Type(u32),                                    // Type0
    Builtin(Builtin),                             // Int
    CaseOf(STerm, Vec<(STerm, STerm)>),           // case x of { y => z }
    Fun(bool, Vec<(bool, STerm)>, STerm),         // move? fun [a] b => c
    App(STerm, STerm),                            // f x
    Pair(STerm, STerm),                           // x, y
    Struct(StructId, Vec<(Spanned<Sym>, STerm)>), // struct { x := 3 }
    Catch(STerm),                                 // catch x
    Raise(STerm),                                 // raise x
    /// Datatypes need a `StructId` too since they create a namespace
    Data(TypeId, StructId, STerm, Vec<(Spanned<Sym>, TagId, STerm)>), // type D: T of C: fun a => D
    Cons(TagId, STerm),                           // C : T
    /// We use RawSym's here because it should work on any record with a field named this
    Project(STerm, Spanned<RawSym>), // r.m
    Block(Vec<Statement>),                        // do { x; y }
    Union(Vec<STerm>),                            // x | y
}
impl Term {
    pub fn uses(&self, s: Sym) -> bool {
        match self {
            Term::Var(x) if *x == s => true,
            Term::Fun(_, v, b) => !v
                .iter()
                .any(|(_,a)| a.binds(s))
                && !b.binds(s)
                && (
                v.iter().any(|(_,a)| a.uses(s))
                || b.uses(s)
            ),
            Term::The(t, u) | Term::App(t, u) | Term::Pair(t, u) => t.uses(s) || u.uses(s),
            Term::Binder(_, Some(t)) | Term::Project(t, _) | Term::Cons(_, t) | Term::Catch(t) | Term::Raise(t) => t.uses(s),
            Term::Struct(_, v) => v.iter().any(|(_, t)| t.uses(s)),
            Term::Data(_, _, t, v) => t.uses(s) || v.iter().any(|(_, _, t)| t.uses(s)),
            Term::Block(v) => v.iter().any(|x| match x {
                Statement::Expr(e) => e.uses(s),
                Statement::Def(Def(_, e)) => e.uses(s),
            }),
            Term::CaseOf(t, v) => t.uses(s) || v.iter().any(|(a, b)| a.uses(s) || b.uses(s)),
            Term::Unit
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Var(_)
            | Term::Binder(_, None)
            // Unions can't bind variables
            | Term::Union(_) => false,
        }
    }

    pub fn binds(&self, s: Sym) -> bool {
        match self {
            Term::Binder(x, _) if *x == s => true,
            Term::Fun(_, v, b) =>
                v.iter().any(|(_,a)| a.uses(s))
                || b.uses(s)
            ,
            Term::The(t, u) | Term::App(t, u) | Term::Pair(t, u) => t.binds(s) || u.binds(s),
            Term::Binder(_, Some(t)) | Term::Project(t, _) | Term::Catch(t) | Term::Raise(t) => t.binds(s),
            Term::Struct(_, v) => v.iter().any(|(x, t)| **x == s || t.binds(s)),
            Term::Data(_, _, t, v) => t.uses(s) || v.iter().any(|(_, _, t)| t.uses(s)),
            Term::Block(v) => v.iter().any(|x| match x {
                Statement::Expr(e) => e.binds(s),
                Statement::Def(Def(x, e)) => **x == s || e.binds(s),
            }),
            // We use `uses` for the pattern side; it's not perfect, though, since we could have a use in a binder or projection
            Term::CaseOf(t, v) => t.binds(s) || v.iter().any(|(a, b)| a.uses(s) || b.binds(s)),
            Term::Unit
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Var(_)
            | Term::Binder(_, None)
            | Term::Cons(_, _)
            // Unions can't bind variables
            | Term::Union(_) => false,
        }
    }

    pub fn traverse(&self, f: impl Fn(&Term) + Copy) {
        f(self);
        match self {
            Term::Fun(_, v, to) => {
                for (_, i) in v {
                    i.traverse(f);
                }
                to.traverse(f);
            }
            Term::The(t, u) | Term::App(t, u) | Term::Pair(t, u) => {
                t.traverse(f);
                u.traverse(f);
            }
            Term::Binder(_, Some(t)) | Term::Project(t, _) | Term::Catch(t) | Term::Raise(t) => {
                t.traverse(f);
            }
            Term::Struct(_, v) => {
                for (_, t) in v.iter() {
                    t.traverse(f);
                }
            }
            _ => (),
        }
    }
}

impl Pretty for Term {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        match self {
            Term::Unit => Doc::start("()").style(Style::Literal),
            Term::Binder(x, Some(t)) => x
                .pretty(ctx)
                .add(":")
                .style(Style::Binder)
                .space()
                .chain(t.pretty(ctx))
                .prec(Prec::Term),
            Term::Binder(x, None) => x.pretty(ctx).add(":").style(Style::Binder).prec(Prec::Term),
            Term::Var(s) => s.pretty(ctx),
            Term::I32(i) => Doc::start(i).style(Style::Literal),
            Term::Type(0) => Doc::start("Type"),
            Term::Type(i) => Doc::start("Type").add(i),
            Term::Builtin(b) => Doc::start(b),
            Term::Catch(t) => Doc::start("catch")
                .style(Style::Keyword)
                .space()
                .chain(t.pretty(ctx))
                .prec(Prec::Term),
            Term::Raise(t) => Doc::start("raise")
                .style(Style::Keyword)
                .space()
                .chain(t.pretty(ctx))
                .prec(Prec::Term),
            Term::CaseOf(val, cases) => Doc::start("case")
                .style(Style::Keyword)
                .space()
                .chain(val.pretty(ctx))
                .space()
                .chain(pretty_block(
                    "of",
                    cases.iter().map(|(pat, body)| {
                        pat.pretty(ctx)
                            .line()
                            .add("=>")
                            .line()
                            .chain(body.pretty(ctx))
                            .indent()
                            .group()
                    }),
                )),
            Term::Fun(m, args, body) => {
                let until_body = if *m {
                    Doc::start("move").space().add("fun")
                } else {
                    Doc::start("fun")
                }
                .style(Style::Keyword)
                .line()
                .chain(Doc::intersperse(
                    args.iter().map(|(implicit, x)| {
                        if *implicit {
                            Doc::start("[").chain(x.pretty(ctx)).add("]").group()
                        } else {
                            x.pretty(ctx)
                        }
                    }),
                    Doc::none().line(),
                ))
                .indent()
                .line()
                .add("=>");
                Doc::either(
                    until_body
                        .clone()
                        .line()
                        .add("  ")
                        .chain(body.pretty(ctx).indent())
                        .group(),
                    until_body.space().chain(body.pretty(ctx).indent()).group(),
                )
                .prec(Prec::Term)
            }
            Term::App(x, y) => x
                .pretty(ctx)
                .nest(Prec::App)
                .space()
                .chain(y.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            Term::Pair(x, y) => Doc::start("(")
                .chain(x.pretty(ctx))
                .add(",")
                .space()
                .chain(y.pretty(ctx))
                .add(")")
                .prec(Prec::Atom),
            Term::Struct(_, v) => pretty_block(
                "struct",
                v.iter().map(|(name, val)| {
                    name.pretty(ctx)
                        .style(Style::Binder)
                        .space()
                        .add(":=")
                        .line()
                        .chain(val.pretty(ctx))
                        .group()
                }),
            ),
            Term::Data(id, _, _, _) => id.pretty(ctx).style(Style::Binder),
            Term::Cons(id, _) => id.pretty(ctx),
            Term::Block(v) => pretty_block(
                "do",
                v.iter().map(|s| match s {
                    Statement::Expr(e) => e.pretty(ctx),
                    Statement::Def(Def(name, val)) => name
                        .pretty(ctx)
                        .style(Style::Binder)
                        .space()
                        .add(":=")
                        .line()
                        .chain(val.pretty(ctx))
                        .group(),
                }),
            ),
            Term::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).add(".").chain(m.pretty(ctx)),
            Term::The(t, x) => Doc::start("the")
                .style(Style::Keyword)
                .line()
                .chain(t.pretty(ctx).nest(Prec::Atom))
                .line()
                .chain(x.pretty(ctx).nest(Prec::Atom))
                .group()
                .indent(),
            Term::Union(v) => Doc::intersperse(
                v.iter().map(|x| x.pretty(ctx)),
                Doc::none().space().add("|").space(),
            ),
        }
    }
}
