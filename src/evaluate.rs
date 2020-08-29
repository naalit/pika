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
        Term::Lam(icit, body) => Val::Lam(icit, Clos(Box::new(env.clone()), body)),
        Term::Pi(icit, ty, body) => {
            let ty = evaluate(*ty, env, mcxt);
            Val::Pi(icit, Box::new(ty), Clos(Box::new(env.clone()), body))
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
            Val::Lam(_, cl) => cl.apply(x, mcxt),
            Val::Error => Val::Error,
            _ => unreachable!(),
        }
    }
}

pub fn inline(val: Val, db: &dyn Compiler) -> Val {
    match val {
        Val::App(h, sp) => match h {
            Var::Top(def) => todo!("evaluate in db"),
            Var::Meta(meta) => {
                // TODO check if solved
                Val::App(h, sp)
            }
            Var::Local(_) | Var::Rec(_) => Val::App(h, sp),
        },
        Val::Pi(icit, mut ty, cl) => {
            // Reuse box
            *ty = inline(*ty, db);
            Val::Pi(icit, ty, cl)
        }
        Val::Fun(mut from, mut to) => {
            // Reuse boxes
            *from = inline(*from, db);
            *to = inline(*to, db);
            Val::Fun(from, to)
        }
        v @ Val::Error | v @ Val::Lam(_, _) | v @ Val::Type => v,
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
        Val::Lam(icit, cl) => Term::Lam(icit, Box::new(cl.quote(mcxt))),
        Val::Pi(icit, ty, cl) => Term::Pi(
            icit,
            Box::new(quote(*ty, enclosing, mcxt)),
            Box::new(cl.quote(mcxt)),
        ),
        Val::Fun(from, to) => Term::Fun(
            Box::new(quote(*from, enclosing, mcxt)),
            Box::new(quote(*to, enclosing, mcxt)),
        ),
        Val::Error => Term::Error,
    }
}
