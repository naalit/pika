use crate::elaborate::MCxt;
use crate::query::*;
use crate::term::*;
use std::collections::VecDeque;

/// This creates a `UVal`, which you can call `inline()` on to turn into an `IVal` if needed.
pub fn evaluate(term: Term, env: &Env, mcxt: &MCxt) -> Val {
    match term {
        Term::Type => Val::Type,
        Term::Var(Var::Local(ix)) => env.val(ix),
        Term::Var(Var::Top(def)) => Val::top(def),
        Term::Var(Var::Rec(id)) => Val::rec(id),
        Term::Var(Var::Meta(meta)) => match mcxt.get_meta(meta) {
            Some(v) => v,
            None => Val::meta(meta),
        },
        Term::Lam(n, icit, ty, body) => Val::Lam(
            icit,
            Box::new(evaluate(*ty, env, mcxt)),
            Box::new(Clos(env.clone(), *body, n)),
        ),
        Term::Pi(n, icit, ty, body) => {
            let ty = evaluate(*ty, env, mcxt);
            Val::Pi(icit, Box::new(ty), Box::new(Clos(env.clone(), *body, n)))
        }
        Term::Fun(from, to) => {
            let from = evaluate(*from, env, mcxt);
            let to = evaluate(*to, env, mcxt);
            Val::Fun(Box::new(from), Box::new(to))
        }
        Term::App(icit, f, x) => {
            let f = evaluate(*f, env, mcxt);
            let x = evaluate(*x, env, mcxt);
            f.app(icit, x, mcxt)
        }
        Term::Error => Val::Error,
    }
}

impl Val {
    pub fn force(self, l: Lvl, db: &dyn Compiler, mcxt: &MCxt) -> Val {
        match self {
            Val::Type => Val::Type,
            Val::Arc(x) => (*x).clone().force(l, db, mcxt),
            Val::App(h, sp, g) => {
                if let Some(v) = g.resolve(h, &sp, l, db, mcxt) {
                    v.force(l, db, mcxt)
                } else {
                    Val::App(h, sp, g)
                }
            }
            Val::Fun(mut a, mut b) => {
                *a = a.force(l, db, mcxt);
                *b = b.force(l, db, mcxt);
                Val::Fun(a, b)
            }
            Val::Error => Val::Error,

            Val::Lam(i, mut ty, mut cl) => {
                *ty = ty.force(l, db, mcxt);
                cl.1 = quote(
                    (*cl).clone().vquote(l, mcxt).force(l, db, mcxt),
                    l.inc(),
                    mcxt,
                );
                Val::Lam(i, ty, cl)
            }
            Val::Pi(i, mut ty, mut cl) => {
                *ty = ty.force(l, db, mcxt);
                cl.1 = quote(
                    (*cl).clone().vquote(l, mcxt).force(l, db, mcxt),
                    l.inc(),
                    mcxt,
                );
                Val::Pi(i, ty, cl)
            }
        }
    }

    pub fn app(self, icit: Icit, x: Val, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, mut sp, _) => {
                sp.push((icit, x));
                // Throw away the old Glued, since that could have been resolved already
                Val::App(h, sp, Glued::new())
            }
            Val::Lam(_, _, cl) => cl.apply(x, mcxt),
            Val::Error => Val::Error,
            Val::Arc(a) => Arc::try_unwrap(a)
                .unwrap_or_else(|a| (*a).clone())
                .app(icit, x, mcxt),
            _ => unreachable!(),
        }
    }
}

pub fn quote(val: Val, enclosing: Lvl, mcxt: &MCxt) -> Term {
    match val {
        Val::Type => Term::Type,
        Val::App(h, sp, _) => {
            let h = match h {
                Var::Local(l) => Term::Var(Var::Local(l.to_ix(enclosing))),
                Var::Top(def) => Term::Var(Var::Top(def)),
                Var::Meta(meta) => Term::Var(Var::Meta(meta)),
                Var::Rec(id) => Term::Var(Var::Rec(id)),
            };
            sp.into_iter().fold(h, |f, (icit, x)| {
                Term::App(icit, Box::new(f), Box::new(quote(x, enclosing, mcxt)))
            })
        }
        Val::Lam(icit, ty, cl) => Term::Lam(
            cl.2,
            icit,
            Box::new(quote(*ty, enclosing, mcxt)),
            Box::new(cl.quote(enclosing, mcxt)),
        ),
        Val::Pi(icit, ty, cl) => Term::Pi(
            cl.2,
            icit,
            Box::new(quote(*ty, enclosing, mcxt)),
            Box::new(cl.quote(enclosing, mcxt)),
        ),
        Val::Fun(from, to) => Term::Fun(
            Box::new(quote(*from, enclosing, mcxt)),
            Box::new(quote(*to, enclosing, mcxt)),
        ),
        Val::Error => Term::Error,
        Val::Arc(x) => quote(
            Arc::try_unwrap(x).unwrap_or_else(|x| (*x).clone()),
            enclosing,
            mcxt,
        ),
    }
}
