use crate::common::*;
use crate::error::Spanned;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum Builtin {
    Int,
}

impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Builtin::Int => write!(f, "Int"),
        }
    }
}

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
    Type,                                         // Type
    Builtin(Builtin),                             // Int
    Fun(STerm, STerm),                            // fn a => x
    App(STerm, STerm),                            // f x
    Pair(STerm, STerm),                           // x, y
    Tag(TagId),                                   // tag
    Struct(StructId, Vec<(Spanned<Sym>, STerm)>), // struct { x := 3 }
    /// We use RawSym's here because it should work on any record with a field named this
    Project(STerm, Spanned<RawSym>), // r.m
    Block(Vec<Statement>),                        // do { x; y }
}
impl Term {
    pub fn traverse(&self, f: impl Fn(&Term) + Copy) {
        f(self);
        match self {
            Term::The(t, u) | Term::Fun(t, u) | Term::App(t, u) | Term::Pair(t, u) => {
                t.traverse(f);
                u.traverse(f);
            }
            Term::Binder(_, Some(t)) | Term::Project(t, _) => {
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

/// Handles prettifying curried functions
/// Does not yet prettify multiple args with the same type (`fun x y: Int => ...` is `fun (x: Int) (y: Int) => ...`)
fn pretty_fun<'a>(mut args: Vec<Doc<'a>>, body: &'a Term, ctx: &Bindings) -> Doc<'a> {
    match body {
        Term::Fun(arg, body) => {
            args.push(arg.pretty(ctx).nest(Prec::Atom));
            pretty_fun(args, body, ctx)
        }
        _ => {
            let until_body = Doc::start("fun")
                .style(Style::Keyword)
                .line()
                .chain(Doc::intersperse(args, Doc::none().line()))
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
    }
}

impl Pretty for Term {
    type Context = Bindings;
    fn pretty(&self, ctx: &Bindings) -> Doc {
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
            Term::Type => Doc::start("Type"),
            Term::Builtin(b) => Doc::start(b),
            Term::Fun(x, y) => pretty_fun(vec![x.pretty(ctx).nest(Prec::Atom)], y, ctx),
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
            Term::Tag(id) => id.pretty(ctx),
            Term::Struct(_, v) => Doc::either(
                Doc::start("struct")
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
                        v.iter().map(|(name, val)| {
                            name.pretty(ctx)
                                .style(Style::Binder)
                                .space()
                                .add(":=")
                                .line()
                                .chain(val.pretty(ctx))
                                .group()
                        }),
                        Doc::none().line(),
                    ))
                    .group()
                    .indent(),
                Doc::start("struct")
                    .style(Style::Keyword)
                    .space()
                    .add("{")
                    .space()
                    .chain(Doc::intersperse(
                        v.iter().map(|(name, val)| {
                            name.pretty(ctx)
                                .style(Style::Binder)
                                .space()
                                .add(":=")
                                .space()
                                .chain(val.pretty(ctx))
                                .group()
                        }),
                        Doc::start(";").space(),
                    ))
                    .space()
                    .add("}")
                    .group(),
            )
            .prec(Prec::Term),
            Term::Block(v) => Doc::either(
                Doc::start("do")
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
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
                        Doc::none().line(),
                    ))
                    .group()
                    .indent(),
                Doc::start("do")
                    .style(Style::Keyword)
                    .space()
                    .add("{")
                    .space()
                    .chain(Doc::intersperse(
                        v.iter().map(|s| match s {
                            Statement::Expr(e) => e.pretty(ctx),
                            Statement::Def(Def(name, val)) => name
                                .pretty(ctx)
                                .style(Style::Binder)
                                .space()
                                .add(":=")
                                .space()
                                .chain(val.pretty(ctx))
                                .group(),
                        }),
                        Doc::start(";").space(),
                    ))
                    .space()
                    .add("}")
                    .group(),
            )
            .prec(Prec::Term),
            Term::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).chain(m.pretty(ctx)),
            Term::The(t, x) => Doc::start("the")
                .style(Style::Keyword)
                .line()
                .chain(t.pretty(ctx).nest(Prec::Atom))
                .line()
                .chain(x.pretty(ctx).nest(Prec::Atom))
                .group()
                .indent(),
        }
    }
}
