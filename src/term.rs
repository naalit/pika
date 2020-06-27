use crate::common::*;
use crate::elab::Elab;
use crate::error::Spanned;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd)]
pub enum Builtin {
    Int,
    Add,
    Sub,
    Mul,
    Div,
}
impl Builtin {
    pub fn is_binop(&self) -> bool {
        match self {
            Builtin::Sub | Builtin::Mul | Builtin::Div | Builtin::Add => true,
            _ => false,
        }
    }

    pub fn get_type(&self) -> Elab {
        match self {
            Builtin::Int => Elab::Type(0),
            Builtin::Sub | Builtin::Mul | Builtin::Div | Builtin::Add => Elab::Fun(
                Clos::default(),
                vec![(
                    vec![Elab::Builtin(Builtin::Int), Elab::Builtin(Builtin::Int)],
                    Elab::Builtin(Builtin::Int),
                    Elab::Type(0),
                )],
            ),
        }
    }
}

impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Builtin::Int => write!(f, "Int"),
            Builtin::Add => write!(f, "(+)"),
            Builtin::Sub => write!(f, "(-)"),
            Builtin::Mul => write!(f, "(*)"),
            Builtin::Div => write!(f, "(/)"),
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
    Type(u32),                                    // Type0
    Builtin(Builtin),                             // Int
    Fun(bool, Vec<(Vec<STerm>, STerm)>),          // move? fun { a b => x; c d => y }
    App(STerm, STerm),                            // f x
    Pair(STerm, STerm),                           // x, y
    Tag(TagId),                                   // tag
    Struct(StructId, Vec<(Spanned<Sym>, STerm)>), // struct { x := 3 }
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
            Term::Fun(_, v) => v
                .iter()
                .filter(|(args, b)| !args.iter().any(|x| x.binds(s)) && !b.binds(s))
                .any(|(args, v)| args.iter().any(|x| x.uses(s)) || v.uses(s)),
            Term::The(t, u) | Term::App(t, u) | Term::Pair(t, u) => t.uses(s) || u.uses(s),
            Term::Binder(_, Some(t)) | Term::Project(t, _) | Term::Cons(_, t) => t.uses(s),
            Term::Struct(_, v) => v.iter().any(|(_, t)| t.uses(s)),
            Term::Data(_, _, t, v) => t.uses(s) || v.iter().any(|(_, _, t)| t.uses(s)),
            Term::Block(v) => v.iter().any(|x| match x {
                Statement::Expr(e) => e.uses(s),
                Statement::Def(Def(_, e)) => e.uses(s),
            }),
            Term::Unit
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Tag(_)
            | Term::Var(_)
            | Term::Binder(_, None)
            // Unions can't bind variables
            | Term::Union(_) => false,
        }
    }

    pub fn binds(&self, s: Sym) -> bool {
        match self {
            Term::Binder(x, _) if *x == s => true,
            Term::Fun(_, v) => v
                .iter()
                .any(|(args, v)| args.iter().any(|x| x.binds(s)) || v.binds(s)),
            Term::The(t, u) | Term::App(t, u) | Term::Pair(t, u) => t.binds(s) || u.binds(s),
            Term::Binder(_, Some(t)) | Term::Project(t, _) => t.binds(s),
            Term::Struct(_, v) => v.iter().any(|(x, t)| **x == s || t.binds(s)),
            Term::Data(_, _, t, v) => t.uses(s) || v.iter().any(|(_, _, t)| t.uses(s)),
            Term::Block(v) => v.iter().any(|x| match x {
                Statement::Expr(e) => e.binds(s),
                Statement::Def(Def(x, e)) => **x == s || e.binds(s),
            }),
            Term::Unit
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Tag(_)
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
            Term::Fun(_, v) => v.iter().for_each(|(args, v)| {
                args.iter().for_each(|x| x.traverse(f));
                v.traverse(f)
            }),
            Term::The(t, u) | Term::App(t, u) | Term::Pair(t, u) => {
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
            Term::Fun(m, v) if v.len() == 1 => {
                let (args, body) = v.first().unwrap();
                let until_body = if *m {
                    Doc::start("move").space().add("fun")
                } else {
                    Doc::start("fun")
                }
                .style(Style::Keyword)
                .line()
                .chain(Doc::intersperse(
                    args.iter().map(|x| x.pretty(ctx)),
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
            Term::Fun(m, v) => pretty_block(
                "fun",
                v.iter().map(|(args, body)| {
                    let until_body = if *m {
                        Doc::start("move").space().add("fun")
                    } else {
                        Doc::start("fun")
                    }
                    .style(Style::Keyword)
                    .line()
                    .chain(Doc::intersperse(
                        args.iter().map(|x| x.pretty(ctx)),
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
                }),
            ),
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
            Term::Data(id, _, _, _) => Doc::start("type")
                .style(Style::Keyword)
                .space()
                .chain(id.pretty(ctx).style(Style::Binder))
                .group(),
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
            Term::Project(r, m) => r.pretty(ctx).nest(Prec::Atom).chain(m.pretty(ctx)),
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
