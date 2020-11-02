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
    pub fn app(self, icit: Icit, x: Val, mcxt: &MCxt) -> Val {
        match self {
            Val::App(h, mut sp) => {
                sp.push((icit, x));
                Val::App(h, sp)
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

pub fn inline(val: Val, db: &dyn Compiler, mcxt: &MCxt) -> Val {
    match val {
        Val::App(h, sp) => {
            let f = match h {
                // TODO can we move the evaluation to Salsa, so it's memoized?
                Var::Top(def) => db.elaborate_def(def).map_or(Val::Error, |i| {
                    evaluate((*i.term).clone(), &mcxt.env(), mcxt)
                }),
                Var::Meta(meta) => match mcxt.get_meta(meta) {
                    Some(v) => v,
                    None => return Val::App(h, sp),
                },
                Var::Local(_) | Var::Rec(_) => return Val::App(h, sp),
            };
            inline(
                sp.into_iter().fold(f, |f, (i, x)| f.app(i, x, mcxt)),
                db,
                mcxt,
            )
        }
        Val::Pi(icit, mut ty, cl) => {
            // Reuse box
            *ty = inline(*ty, db, mcxt);
            Val::Pi(icit, ty, cl)
        }
        Val::Fun(mut from, mut to) => {
            // Reuse boxes
            *from = inline(*from, db, mcxt);
            *to = inline(*to, db, mcxt);
            Val::Fun(from, to)
        }
        v @ Val::Error | v @ Val::Lam(_, _, _) | v @ Val::Type => v,
        Val::Arc(x) => inline(
            Arc::try_unwrap(x).unwrap_or_else(|x| (*x).clone()),
            db,
            mcxt,
        ),
    }
}

pub fn quote(val: Val, enclosing: Lvl, mcxt: &MCxt) -> Term {
    match val {
        Val::Type => Term::Type,
        Val::App(h, sp) => {
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
