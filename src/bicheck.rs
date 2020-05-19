//! Bidirectional type checking
use crate::common::*;
use crate::error::*;
use crate::term::*;

#[derive(Debug, Clone)]
pub enum TypeError {
    Synth(STerm),
    NotFunction(STerm),
    NotPattern(STerm),
    NotSubtype(STerm, STerm),
    NotFound(Spanned<Sym>),
}
impl TypeError {
    pub fn to_error(self, file: FileId, b: &Bindings) -> Error {
        match self {
            TypeError::Synth(t) => Error::new(
                file,
                format!(
                    "Type error: Could not synthesize type for '{}': try adding an annotation",
                    WithContext(b, &*t)
                ),
                t.span(),
                "try adding an annotation here",
            ),
            TypeError::NotFunction(t) => Error::new(
                file,
                format!("Type error: Not a function type: '{}", WithContext(b, &*t)),
                t.span(),
                "Not a function",
            ),
            TypeError::NotPattern(t) => Error::new(
                file,
                format!("Type error: Not a valid pattern: '{}", WithContext(b, &*t)),
                t.span(),
                "Not a valid pattern",
            ),
            TypeError::NotSubtype(sub, sup) => Error::new(
                file,
                format!(
                    "Type error: Could not match types: '{}' and '{}'",
                    WithContext(b, &*sub),
                    WithContext(b, &*sup)
                ),
                sub.span(),
                format!("this has type '{}'", WithContext(b, &*sub)),
            )
            .with_label(
                file,
                sup.span(),
                format!("required type '{}'", WithContext(b, &*sup)),
            ),
            TypeError::NotFound(s) => Error::new(
                file,
                format!("Error: variable not found: '{}'", b.resolve(*s),),
                s.span(),
                format!("not found"),
            ),
        }
    }
}
impl CDisplay for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter, b: &Bindings) -> std::fmt::Result {
        match self {
            TypeError::Synth(t) => write!(
                f,
                "Could not synthesize type for '{}': try adding an annotation",
                WithContext(b, &**t)
            ),
            TypeError::NotFunction(t) => {
                write!(f, "Not a function type: '{}'", WithContext(b, &**t))
            }
            TypeError::NotPattern(t) => {
                write!(f, "Not a valid pattern: '{}'", WithContext(b, &**t))
            }
            TypeError::NotSubtype(sub, sup) => write!(
                f,
                "Could not match types: '{}' and '{}'",
                WithContext(b, &**sub),
                WithContext(b, &**sup)
            ),
            TypeError::NotFound(s) => write!(f, "Not found: '{}'", b.resolve(**s),),
        }
    }
}

/// Attempt to synthesize a type for 't'
pub fn synth(t: &STerm, env: &mut Env) -> Result<STerm, TypeError> {
    match &**t {
        Term::Type | Term::Builtin(Builtin::Int) => Ok(t.copy_span(Term::Type)),
        Term::Var(x) => env
            .ty(*x)
            .cloned()
            .ok_or_else(|| TypeError::NotFound(t.copy_span(*x))),
        Term::I32(_) => Ok(t.copy_span(Term::Builtin(Builtin::Int))),
        Term::Unit => Ok(t.clone()),
        Term::Pair(x, y) => {
            // TODO this better
            let mut menv = env.clone();
            x.apply_defs(&mut menv);
            Ok(t.copy_span(Term::Pair(synth(x, env)?, synth(y, &mut menv)?)))
        }
        Term::Let(x, t, u) => {
            let tt = synth(t, env)?;
            env.with_ty(*x, tt, |env| {
                env.with_val(*x, t.clone(), |env| synth(u, env))
            })
        }
        Term::App(f, x) => {
            let a = synth(f, env)?;
            match &*a {
                Term::Fun(from, to) => {
                    check(x, &from, env)?;
                    Ok(to.clone())
                }
                _ => Err(TypeError::NotFunction(a)),
            }
        }
        Term::Fun(x, y) => {
            // TODO this better
            let mut menv = env.clone();
            x.apply_defs(&mut menv);
            Ok(t.copy_span(Term::Fun(x.clone(), synth(y, &mut menv)?)))
        }
        Term::Binder(_, t) => synth(t, env),
        _ => Err(TypeError::Synth(t.clone())),
    }
}

pub fn check(term: &STerm, typ: &STerm, env: &mut Env) -> Result<(), TypeError> {
    match (&**term, &**typ) {
        (Term::Unit, Term::Unit)
        | (Term::Type, Term::Type)
        | (Term::Builtin(Builtin::Int), Term::Type) => Ok(()),
        (Term::Binder(_, t), _) => check(t, typ, env),
        (Term::Fun(x, b), Term::Fun(y, to)) => {
            // TODO: Pattern matching!
            match &**x {
                Term::Binder(a, t) => {
                    if y.subtype_of(t, env)? {
                        env.with_ty(*a, t.clone(), |env| check(b, to, env))
                    } else {
                        Err(TypeError::NotSubtype(y.clone(), t.clone()))
                    }
                }
                Term::Var(a) => env.with_ty(*a, y.clone(), |env| check(b, to, env)),
                _ => Err(TypeError::NotPattern(x.clone())),
            }
        }
        (Term::App(f, x), _) => {
            let tx = synth(x, env)?;
            check(f, &typ.copy_span(Term::Fun(tx, typ.clone())), env)
        }
        (_, _) => {
            let t = synth(term, env)?;
            // Is it guaranteed to be a `typ`?
            if t.subtype_of(&typ, env)? {
                Ok(())
            } else {
                Err(TypeError::NotSubtype(t, typ.clone()))
            }
        }
    }
}
