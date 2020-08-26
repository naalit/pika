use crate::error::*;
use crate::evaluate::*;
use crate::query::*;
use crate::term::*;
use std::sync::Arc;

pub fn elaborate_def(db: &dyn Compiler, def: DefId) -> Result<(Arc<Term>, Arc<VTy>), DefError> {
    let (predef, cxt) = db.lookup_intern_def(def);
    let file = cxt.file(db);
    match &*predef {
        PreDef::Val(_, ty, val) | PreDef::Impl(_, ty, val) => {
            match check(ty, &Val::Type, db, cxt) {
                Ok(ty) => {
                    let ty = evaluate(ty, &cxt.env(db));
                    match check(val, &ty, db, cxt) {
                        Ok(val) => Ok((Arc::new(val), Arc::new(ty))),
                        Err(e) => {
                            db.report_error(e.to_error(file, db));
                            Err(DefError::ElabError)
                        }
                    }
                }
                Err(e) => {
                    db.report_error(e.to_error(file, db));
                    // We can still try to infer the type
                    match infer(val, db, cxt) {
                        Ok((val, ty)) => Ok((Arc::new(val), Arc::new(ty))),
                        Err(e) => {
                            db.report_error(e.to_error(file, db));
                            Err(DefError::ElabError)
                        }
                    }
                }
            }
        }
        PreDef::Fun(_, args, body_ty, body) => {
            let mut cxt = cxt;
            let mut targs = Vec::new();
            for (name, icit, ty) in args {
                let ty = match check(ty, &Val::Type, db, cxt) {
                    Ok(x) => x,
                    Err(e) => {
                        db.report_error(e.to_error(file, db));
                        // TODO make a meta? or just call `infer()`?
                        Term::Error
                    }
                };
                let vty = evaluate(ty, &cxt.env(db));
                targs.push((*icit, vty.clone()));
                cxt = cxt.define(*name, NameInfo::Local(vty), db);
            }
            let body_ty = match check(body_ty, &Val::Type, db, cxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db));
                    // TODO make a meta? or just call `infer()`?
                    Term::Error
                }
            };
            let vty = evaluate(body_ty, &cxt.env(db));
            let body = match check(body, &vty, db, cxt) {
                Ok(x) => x,
                Err(e) => {
                    db.report_error(e.to_error(file, db));
                    return Err(DefError::ElabError);
                }
            };
            Ok((
                Arc::new(
                    targs
                        .iter()
                        .rfold(body, |body, (icit, _)| Term::Lam(*icit, Box::new(body))),
                ),
                Arc::new(
                    targs
                        .into_iter()
                        .rfold((vty, cxt.size(db)), |(to, size), (icit, from)| {
                            (
                                Val::Pi(
                                    icit,
                                    Box::new(from),
                                    Clos(Env::new(size), Box::new(quote(to, size))),
                                ),
                                size.dec(),
                            )
                        })
                        .0,
                ),
            ))
        }
        PreDef::Type(_, _, _) => todo!("data types"),
        PreDef::Expr(e) => {
            if let Err(e) = infer(e, db, cxt) {
                db.report_error(e.to_error(file, db));
            }
            Err(DefError::NoValue)
        }
        PreDef::FunDec(_, from, to) => {
            for (_, _, from) in from {
                if let Err(e) = check(from, &Val::Type, db, cxt) {
                    db.report_error(e.to_error(file, db));
                }
            }
            if let Err(e) = check(to, &Val::Type, db, cxt) {
                db.report_error(e.to_error(file, db));
            }
            Err(DefError::NoValue)
        }
        PreDef::ValDec(_, ty) => {
            if let Err(e) = check(ty, &Val::Type, db, cxt) {
                db.report_error(e.to_error(file, db));
            }
            Err(DefError::NoValue)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    NotFound(Spanned<Name>),
    NotFunction(Spanned<VTy>),
    Unify(Spanned<VTy>, VTy),
}
impl TypeError {
    fn to_error(self, file: FileId, db: &dyn Compiler) -> Error {
        match self {
            TypeError::NotFound(n) => Error::new(
                file,
                format!("Name not found in scope: {}", n.get(db)),
                n.span(),
                "not found",
            ),
            TypeError::NotFunction(t) => Error::new(
                file,
                format!("Expected function type in application, but got: <TODO pretty val>"),
                t.span(),
                "not a function",
            ),
            TypeError::Unify(a, b) => Error::new(
                file,
                format!("Could not match types, expected <B>, got <A>"),
                a.span(),
                format!("expected <B>"),
            ),
        }
    }
}

/// A three-value logic type, useful for analysis with limited information.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum TBool {
    Yes,
    No,
    Maybe,
}
impl TBool {
    /// Converts to a `bool`, panicking on `Maybe`.
    pub fn not_maybe(self) -> bool {
        match self {
            Yes => true,
            No => false,
            Maybe => panic!("Called `TBool::not_maybe()` on `Maybe`"),
        }
    }
}
pub use TBool::{Maybe, No, Yes};
impl std::ops::BitOr for TBool {
    type Output = TBool;

    fn bitor(self, rhs: TBool) -> TBool {
        match (self, rhs) {
            (Yes, _) | (_, Yes) => Yes,
            (No, No) => No,
            _ => Maybe,
        }
    }
}
impl std::ops::BitAnd for TBool {
    type Output = TBool;

    fn bitand(self, rhs: TBool) -> TBool {
        match (self, rhs) {
            (No, _) | (_, No) => No,
            (Yes, Yes) => Yes,
            _ => Maybe,
        }
    }
}
impl std::ops::BitAnd<bool> for TBool {
    type Output = TBool;

    fn bitand(self, rhs: bool) -> TBool {
        self & TBool::from(rhs)
    }
}
impl From<bool> for TBool {
    fn from(b: bool) -> TBool {
        match b {
            true => Yes,
            false => No,
        }
    }
}

fn p_unify(a: Val, b: Val, db: &dyn Compiler) -> TBool {
    match (a, b) {
        (Val::Error, _) | (_, Val::Error) => Yes,
        (Val::Type, Val::Type) => Yes,

        (Val::App(h, v), Val::App(h2, v2)) if h == h2 => {
            let mut r = Yes;
            for ((i, a), (i2, b)) in v.into_iter().zip(v2.into_iter()) {
                assert_eq!(i, i2);
                r = r & p_unify(a, b, db);
            }
            r
        }

        // Since our terms are locally nameless (we're using De Bruijn levels), we automatically get alpha equivalence.
        // Also, we call `unify` instead of `p_unify` here so we can `inline()` the values we're creating here if necessary.
        (Val::Lam(_, cl), Val::Lam(_, cl2)) => unify(cl.vquote(), cl2.vquote(), db).into(),

        // If one side is a lambda, the other side just needs to unify to the same thing when we apply it to the same thing
        (Val::Lam(icit, cl), t) | (t, Val::Lam(icit, cl)) => {
            let var = Val::local(cl.env_size());
            unify(cl.apply(var.clone()), t.app(icit, var), db).into()
        }

        (Val::Pi(i, ty, cl), Val::Pi(i2, ty2, cl2)) if i == i2 => {
            p_unify(*ty, *ty2, db) & unify(cl.vquote(), cl2.vquote(), db)
        }
        (Val::Pi(Icit::Expl, ty, cl), Val::Fun(from, to))
        | (Val::Fun(from, to), Val::Pi(Icit::Expl, ty, cl)) => {
            // TODO: I'm not 100% this is right
            p_unify(*ty, *from, db) & unify(cl.vquote(), *to, db)
        }
        (Val::Fun(a, b), Val::Fun(a2, b2)) => p_unify(*a, *b, db) & p_unify(*a2, *b2, db),

        // Solve metas
        // TODO make order not matter (compare metas?)
        (Val::App(Head::VarMeta(m), sp), t) | (t, Val::App(Head::VarMeta(m), sp)) => {
            todo!("solve metas")
        }

        // If the reason we can't unify is that one side is a top variable, then we can try again after inlining.
        (Val::App(Head::VarTop(_), _), _) | (_, Val::App(Head::VarTop(_), _)) => Maybe,

        // If that's not the reason, then we know inlining won't help.
        _ => No,
    }
}

/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn unify(a: Val, b: Val, db: &dyn Compiler) -> bool {
    match p_unify(a.clone(), b.clone(), db) {
        Yes => true,
        No => false,
        Maybe => p_unify(inline(a, db), inline(b, db), db).not_maybe(),
    }
}

pub fn infer(pre: &Pre, db: &dyn Compiler, cxt: Cxt) -> Result<(Term, VTy), TypeError> {
    match &**pre {
        Pre_::Type => Ok((Term::Type, Val::Type)),
        Pre_::Var(name) => match cxt.lookup(*name, db) {
            Some(NameResult::Def(def)) => {
                match db.def_type(def) {
                    Ok(ty) => Ok((Term::VarTop(def), (*ty).clone())),
                    // If something else had a type error, try to keep going anyway and maybe catch more
                    Err(DefError::ElabError) => Ok((Term::Error, todo!("hole: add meta"))),
                    Err(DefError::NoValue) => Err(TypeError::NotFound(pre.copy_span(*name))),
                }
            }
            Some(NameResult::Local(ix, ty)) => Ok((Term::VarLocal(ix), ty)),
            None => Err(TypeError::NotFound(pre.copy_span(*name))),
        },
        Pre_::Lam(name, icit, ty, body) => {
            let ty = check(ty, &Val::Type, db, cxt)?;
            let vty = evaluate(ty, &cxt.env(db));
            // TODO Rc to get rid of the clone()?
            let cxt = cxt.define(*name, NameInfo::Local(vty.clone()), db);
            let (body, bty) = infer(body, db, cxt)?;
            Ok((
                Term::Lam(*icit, Box::new(body)),
                Val::Pi(
                    *icit,
                    Box::new(vty),
                    // `inc()` since we're wrapping it in a lambda
                    Clos(cxt.env(db), Box::new(quote(bty, cxt.size(db).inc()))),
                ),
            ))
        }
        Pre_::Pi(name, icit, ty, ret) => {
            let ty = check(ty, &Val::Type, db, cxt)?;
            // TODO Rc to get rid of the clone()?
            let vty = evaluate(ty.clone(), &cxt.env(db));
            let cxt = cxt.define(*name, NameInfo::Local(vty), db);
            let ret = check(ret, &Val::Type, db, cxt)?;
            Ok((Term::Pi(*icit, Box::new(ty), Box::new(ret)), Val::Type))
        }
        Pre_::Fun(from, to) => {
            let from = check(from, &Val::Type, db, cxt)?;
            let to = check(to, &Val::Type, db, cxt)?;
            Ok((Term::Fun(Box::new(from), Box::new(to)), Val::Type))
        }
        Pre_::App(icit, f, x) => {
            let (f, fty) = infer(f, db, cxt)?;
            match fty {
                Val::Pi(icit2, from, cl) => {
                    // TODO insert metas !?
                    let x = check(x, &*from, db, cxt)?;
                    // TODO Rc to get rid of the clone()?
                    let to = cl.apply(evaluate(x.clone(), &cxt.env(db)));
                    Ok((Term::App(*icit, Box::new(f), Box::new(x)), to))
                }
                Val::Fun(from, to) => {
                    let x = check(x, &*from, db, cxt)?;
                    Ok((Term::App(*icit, Box::new(f), Box::new(x)), *to))
                }
                // The type was already Error, so we'll leave it there, not introduce a meta
                Val::Error => Ok((Term::Error, Val::Error)),
                fty => return Err(TypeError::NotFunction(pre.copy_span(fty))),
            }
        }
        Pre_::Do(_) => todo!("elaborate do"),
        Pre_::Struct(_) => todo!("elaborate struct"),
        Pre_::Hole => todo!("meta support"),
    }
}

pub fn check(pre: &Pre, ty: &VTy, db: &dyn Compiler, cxt: Cxt) -> Result<Term, TypeError> {
    match (&**pre, ty) {
        (Pre_::Lam(n, i, ty, body), Val::Pi(i2, ty2, cl)) if i == i2 => {
            let vty = check(ty, &Val::Type, db, cxt)?;
            let vty = evaluate(vty, &cxt.env(db));
            if !unify(vty.clone(), (**ty2).clone(), db) {
                return Err(TypeError::Unify(ty.copy_span(vty), (**ty2).clone()));
            }
            if cxt.size(db) != cl.env_size() {
                eprintln!("Warning: {:?} vs {:?}", cxt.size(db), cl.env_size())
            }
            let cxt = cxt.define(*n, NameInfo::Local(vty), db);
            // TODO not clone ??
            let body = check(body, &cl.clone().vquote(), db, cxt)?;
            Ok(Term::Lam(*i, Box::new(body)))
        }

        (Pre_::Lam(n, Icit::Expl, ty, body), Val::Fun(ty2, body_ty)) => {
            let vty = check(ty, &Val::Type, db, cxt)?;
            let vty = evaluate(vty, &cxt.env(db));
            if !unify(vty.clone(), (**ty2).clone(), db) {
                return Err(TypeError::Unify(ty.copy_span(vty), (**ty2).clone()));
            }
            let cxt = cxt.define(*n, NameInfo::Local(vty), db);
            let body = check(body, &*body_ty, db, cxt)?;
            Ok(Term::Lam(Icit::Expl, Box::new(body)))
        }

        // We implicitly insert lambdas so `\x.x : [a] -> a -> a` typechecks
        (_, Val::Pi(Icit::Impl, ty, cl)) => {
            // TODO should we preserve names further?
            let cxt = cxt.define(
                db.intern_name("_".to_string()),
                NameInfo::Local((**ty).clone()),
                db,
            );
            let body = check(pre, &cl.clone().vquote(), db, cxt)?;
            Ok(Term::Lam(Icit::Impl, Box::new(body)))
        }

        _ => {
            let (term, i_ty) = infer(pre, db, cxt)?;
            // TODO should we take `ty` by value?
            // We still need to clone to use it the error though...
            // Maybe unification returns an error itself?
            if unify(ty.clone(), i_ty.clone(), db) {
                Ok(term)
            } else {
                Err(TypeError::Unify(pre.copy_span(ty.clone()), i_ty))
            }
        }
    }
}
