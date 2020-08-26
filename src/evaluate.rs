use crate::query::*;
use crate::term::*;
use std::collections::VecDeque;

/// This creates a `UVal`, which you can call `inline()` on to turn into an `IVal` if needed.
pub fn evaluate(term: Term, env: &Env) -> Val {
    match term {
        Term::Type => Val::Type,
        Term::VarLocal(ix) => env.val(ix),
        Term::VarTop(def) => Val::top(def),
        Term::VarMeta(meta) => {
            // TODO check if solved
            Val::meta(meta)
        }
        Term::Lam(icit, body) => Val::Lam(icit, Clos(env.clone(), body)),
        Term::Pi(icit, ty, body) => {
            let ty = evaluate(*ty, env);
            Val::Pi(icit, Box::new(ty), Clos(env.clone(), body))
        }
        Term::Fun(from, to) => {
            let from = evaluate(*from, env);
            let to = evaluate(*to, env);
            Val::Fun(Box::new(from), Box::new(to))
        }
        Term::App(icit, f, x) => {
            let f = evaluate(*f, env);
            let x = evaluate(*x, env);
            f.app(icit, x)
        }
        Term::Error => Val::Error,
    }
}

impl Val {
    pub fn app(self, icit: Icit, x: Val) -> Val {
        match self {
            Val::App(h, mut sp) => {
                sp.push((icit, x));
                Val::App(h, sp)
            }
            Val::Lam(_, cl) => cl.apply(x),
            Val::Error => Val::Error,
            _ => unreachable!(),
        }
    }
}

pub fn inline(val: Val, db: &dyn Compiler) -> Val {
    match val {
        Val::App(h, sp) => match h {
            Head::VarTop(def) => todo!("evaluate in db"),
            Head::VarMeta(meta) => {
                // TODO check if solved
                Val::App(h, sp)
            }
            Head::VarLocal(_) => Val::App(h, sp),
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

pub fn quote(val: Val, enclosing: Lvl) -> Term {
    match val {
        Val::Type => Term::Type,
        Val::App(h, sp) => {
            let h = match h {
                Head::VarLocal(l) => Term::VarLocal(l.to_ix(enclosing)),
                Head::VarTop(def) => Term::VarTop(def),
                Head::VarMeta(meta) => Term::VarMeta(meta),
            };
            sp.into_iter().fold(h, |f, (icit, x)| {
                Term::App(icit, Box::new(f), Box::new(quote(x, enclosing)))
            })
        }
        Val::Lam(icit, cl) => Term::Lam(icit, Box::new(cl.quote())),
        Val::Pi(icit, ty, cl) => {
            Term::Pi(icit, Box::new(quote(*ty, enclosing)), Box::new(cl.quote()))
        }
        Val::Fun(from, to) => Term::Fun(
            Box::new(quote(*from, enclosing)),
            Box::new(quote(*to, enclosing)),
        ),
        Val::Error => Term::Error,
    }
}
