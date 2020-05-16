//! Bidirectional type checking
use crate::term::*;
use crate::error::*;

#[derive(Debug, Clone)]
pub enum TypeError {
    Synth(STerm),
    NotFunction(STerm),
    NotSubtype(STerm, STerm),
}
impl TypeError {
    pub fn to_error(self, file: FileId) -> Error {
        match self {
            TypeError::Synth(t) => Error::new(file, format!("Type error: Could not synthesize type for '{}': try adding an annotation", *t), t.span(), "try adding an annotation here"),
            TypeError::NotFunction(t) => Error::new(file, format!("Type error: Not a function type: '{}", *t), t.span(), "Not a function"),
            TypeError::NotSubtype(sub, sup) => Error::new(file, format!("Type error: Could not match types: '{}' and '{}'", *sub, *sup), sub.span(), format!("this has type '{}'", *sub)),
        }
    }
}
impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TypeError::Synth(t) => write!(f, "Could not synthesize type for '{}': try adding an annotation", **t),
            TypeError::NotFunction(t) => write!(f, "Not a function type: '{}'", **t),
            TypeError::NotSubtype(sub, sup) => write!(f, "Could not match types: '{}' and '{}'", **sub, **sup),
        }
    }
}

/// Attempt to synthesize a type for 't'
pub fn synth(t: &STerm, env: &mut Env) -> Result<STerm, TypeError> {
    match &**t {
        Term::Type
        | Term::Builtin(Builtin::Int)
        // TODO do we make sure the arrow type arguments are sensible?
        | Term::Arrow(_, _) => Ok(t.copy_span(Term::Type)),
        Term::Var(x) => Ok(env.get(x).unwrap().clone()),
        Term::I32(_) => Ok(t.copy_span(Term::Builtin(Builtin::Int))),
        Term::Unit => Ok(t.clone()),
        Term::Pair(x, y) => Ok(t.copy_span(Term::Pair(synth(x, env)?, synth(y, env)?))),
        Term::App(f, x) => {
            let a = synth(f, env)?;
            match &*a {
                Term::Arrow(from, to) => {
                    check(x, &from, env)?;
                    Ok(to.clone())
                }
                _ => Err(TypeError::NotFunction(a)),
            }
        }
        // Term::Fun(x, y) => {
        // }
        Term::Ann(x, y) => {
            check(x, y, env)?;
            Ok(y.clone())
        }
        _ => Err(TypeError::Synth(t.clone())),
    }
}

pub fn check(term: &STerm, typ: &STerm, env: &mut Env) -> Result<(), TypeError> {
    match (&**term, &**typ) {
        (Term::Unit, Term::Unit)
        | (Term::Type, Term::Type)
        | (Term::Builtin(Builtin::Int), Term::Type) => Ok(()),
        (Term::Fun(x, b), Term::Arrow(from, to)) => {
            env.with(*x, from.clone(), |env| check(b, to, env))
        }
        (_, _) => {
            let t = synth(term, env)?;
            // Is it guaranteed to be a `typ`?
            if t.subtype_of(&typ, env) {
                Ok(())
            } else {
                Err(TypeError::NotSubtype(t, typ.clone()))
            }
        }
    }
}
