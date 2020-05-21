//! Bidirectional type checking
use crate::common::*;
use crate::error::*;
use crate::eval::*;
use crate::term::*;
use std::collections::HashMap;

/// The context for typechecking
///
/// This includes an evaluation `Context` because we often need to evaluate types
pub struct TEnv {
    tys: HashMap<Sym, Value>,
    pub ctx: Context,
}
impl TEnv {
    pub fn new(ctx: Context) -> Self {
        TEnv {
            tys: HashMap::new(),
            ctx,
        }
    }

    /// Get a type from the `TEnv`, calling `cloned()` on it and returning the owned value
    /// Analogous to `Context::get_cloned()`
    fn ty_cloned(&mut self, s: Sym) -> Option<Value> {
        let x = self.tys.remove(&s)?;
        let t = x.cloned(&mut self.ctx);
        self.tys.insert(s, x);
        Some(t)
    }
}

/// An error produced in type checking
pub enum TypeError {
    /// We couldn't synthesize a type for the given term
    Synth(STerm),
    /// We tried to apply the given term, but it's not a function
    /// The `Value` here is the type
    NotFunction(Spanned<Value>),
    /// The first value needs to be a subtype of the second one, but it's not
    NotSubtype(Spanned<Value>, Value),
    /// `NotSubtype` with flipped span information
    NotSubtypeF(Value, Spanned<Value>),
    /// We couldn't find a type for the given variable
    /// Currently, this only occurs when using bindings without a type, where we couldn't infer the type
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
            TypeError::NotSubtype(sub, sup) => Error::new(
                file,
                format!(
                    "Type error: Could not match types: '{}' and '{}'",
                    WithContext(b, &*sub),
                    WithContext(b, &sup)
                ),
                sub.span(),
                format!("this has type '{}'", WithContext(b, &*sub)),
            ),
            TypeError::NotSubtypeF(sub, sup) => Error::new(
                file,
                format!(
                    "Type error: Could not match types: '{}' and '{}'",
                    WithContext(b, &sub),
                    WithContext(b, &*sup)
                ),
                sup.span(),
                format!("this has type '{}'", WithContext(b, &*sup)),
            ),
            TypeError::NotFound(s) => Error::new(
                file,
                format!(
                    "Type error: could not find type for variable: '{}'",
                    b.resolve(*s),
                ),
                s.span(),
                format!("type not found"),
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
            TypeError::NotSubtype(sub, sup) => write!(
                f,
                "Could not match types: '{}' and '{}'",
                WithContext(b, &**sub),
                WithContext(b, &*sup)
            ),
            TypeError::NotSubtypeF(sub, sup) => write!(
                f,
                "Could not match types: '{}' and '{}'",
                WithContext(b, &*sub),
                WithContext(b, &**sup)
            ),
            TypeError::NotFound(s) => {
                write!(f, "Type not found for varible: '{}'", b.resolve(**s),)
            }
        }
    }
}

/// Attempt to synthesize a type for 't'
pub fn synth(t: &STerm, env: &mut TEnv) -> Result<Value, TypeError> {
    #[cfg(feature = "logging")]
    println!("synth ({})", WithContext(&env.ctx.bindings, &**t));

    match &**t {
        Term::Type | Term::Builtin(Builtin::Int) => Ok(Value::Type),
        Term::Var(x) => env
            .ty_cloned(*x)
            .ok_or_else(|| TypeError::NotFound(t.copy_span(*x))),
        Term::I32(_) => Ok(Value::Builtin(Builtin::Int)),
        Term::Unit => Ok(Value::Unit),
        Term::Pair(x, y) => {
            // TODO this doesn't cover dependent pairs
            Ok(Value::Pair(
                Box::new(synth(x, env)?),
                Box::new(synth(y, env)?),
            ))
        }
        Term::Let(x, t, u) => {
            let tt = synth(t, env)?;
            env.tys.insert(*x, tt);
            let tv = t.reduce(&mut env.ctx);
            env.ctx.vals.insert(*x, tv);
            synth(u, env)
        }
        Term::App(f, x) => {
            let a = synth(f, env)?;
            match &a {
                Value::Fun(from, to) => {
                    check(x, &from, env)?;
                    // Stick the value in in case it's dependent
                    let mut to = to.cloned(&mut env.ctx);
                    let x = x.reduce(&mut env.ctx);
                    from.do_match(&x, &mut env.ctx);
                    to.update(&mut env.ctx);
                    Ok(to)
                }
                _ => Err(TypeError::NotFunction(f.copy_span(a))),
            }
        }
        Term::Fun(x, y) => {
            // Make sure it's well typed before reducing it
            check(x, &Value::Type, env)?;
            let x = x.reduce(&mut env.ctx);
            // Match it with itself to apply the types
            x.match_types(&x, env);
            Ok(Value::Fun(Box::new(x), Box::new(synth(y, env)?)))
        }
        Term::The(t, u) => {
            // Make sure it's well typed before reducing it
            check(t, &Value::Type, env)?;
            let t = t.reduce(&mut env.ctx);
            check(u, &t, env)?;
            Ok(t)
        }
        Term::Binder(_, Some(t)) => synth(t, env),
        _ => Err(TypeError::Synth(t.clone())),
    }
}

/// Checks the given term against the given type
pub fn check(term: &STerm, typ: &Value, env: &mut TEnv) -> Result<(), TypeError> {
    #[cfg(feature = "logging")]
    println!("check ({}) :: ({})", WithContext(&env.ctx.bindings, &**term), WithContext(&env.ctx.bindings, typ));

    match (&**term, typ) {
        (_, Value::Type) => {
            let t = term.reduce(&mut env.ctx);
            if t.is_type() { Ok(()) } else { Err(TypeError::NotSubtype(term.copy_span(t), Value::Type)) }
        }

        (Term::Unit, Value::Unit) => Ok(()),

        (Term::Pair(x, y), Value::Pair(tx, ty)) => {
            // TODO dependent pairs don't really work
            check(x, tx, env)?;
            check(y, ty, env)
        }

        // As far as we know, it could be any type
        (Term::Binder(_, None), _) if typ.subtype_of(&Value::Type, env) => Ok(()),

        (Term::Binder(_, Some(t)), _) => check(t, typ, env),
        (Term::Fun(x, b), Value::Fun(y, to)) => {
            // Make sure it's well typed before reducing it
            check(x, &Value::Type, env)?;
            let xr = x.reduce(&mut env.ctx);
            // Because patterns are types, match checking amounts to subtype checking
            if y.subtype_of(&xr, env) {
                xr.match_types(y, env);
                check(b, to, env)
            } else {
                Err(TypeError::NotSubtypeF(
                    y.cloned(&mut env.ctx),
                    x.copy_span(xr),
                ))
            }
        }
        (_, _) => {
            let t = synth(term, env)?;
            // Is it guaranteed to be a `typ`?
            if t.subtype_of(&typ, env) {
                Ok(())
            } else {
                Err(TypeError::NotSubtype(
                    term.copy_span(t),
                    typ.cloned(&mut env.ctx),
                ))
            }
        }
    }
}

impl Value {
    /// Like do_match(), but fills in the types instead of values
    fn match_types(&self, other: &Value, env: &mut TEnv) {
        use Value::*;
        match (self, other) {
            // Since we match it against itself to apply binder types
            (Binder(na, _), Binder(nb, t)) if na == nb => {
                if let Some(t) = t {
                    #[cfg(feature = "logging")]
                    println!("env: {} : {}", WithContext(&env.ctx.bindings, self), WithContext(&env.ctx.bindings, &**t));

                    let t = t.cloned(&mut env.ctx);
                    env.tys.insert(*na, t);
                }
            }
            // For alpha-equivalence - we need symbols in our body to match symbols in the other body if they're defined as the same
            (_, Binder(x, t)) => {
                self.do_match(&Var(*x), &mut env.ctx);
                if let Some(t) = t {
                    self.match_types(t, env);
                }
            }
            (Binder(s, _), _) => {
                #[cfg(feature = "logging")]
                println!("env: {} : {}", WithContext(&env.ctx.bindings, self), WithContext(&env.ctx.bindings, other));

                let other = other.cloned(&mut env.ctx);
                env.tys.insert(*s, other);
            }
            (Var(x), _) => {
                if let Some(x) = env.ctx.get_cloned(*x) {
                    x.match_types(other, env);
                }
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.match_types(bx, env);
                ay.match_types(by, env);
            }
            // We will allow this for now, and see if it causes any problems
            (App(af, ax), App(bf, bx)) => {
                af.match_types(bf, env);
                ax.match_types(bx, env);
            }
            _ => (),
        }
    }

    /// *Could* it be a type?
    fn is_type(&self) -> bool {
        match self {
            Value::Type | Value::Unit | Value::Builtin(Builtin::Int) => true,
            Value::Fun(_, x) => x.is_type(),
            Value::Pair(x, y) => x.is_type() && y.is_type(),
            Value::Binder(_, _) => true,
            // We're not sure, but it could be
            Value::Var(_) => true,
            _ => false,
        }
    }

    /// Is this a subtype of Type?
    fn is_type_type(&self, env: &TEnv) -> bool {
        match self {
            Value::Type => true,
            Value::Var(x) => env.tys.get(x).map_or(false, |x| x.is_type_type(env)),
            Value::Pair(x, y) => x.is_type_type(env) && y.is_type_type(env),
            Value::Fun(_, x) => x.is_type_type(env),
            Value::Binder(_, None) => true,
            Value::Binder(_, Some(t)) => t.is_type_type(env),
            _ => false,
        }
    }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality
    pub fn subtype_of(&self, sup: &Value, env: &mut TEnv) -> bool {
        if !self.is_type() {
            return false;
        }
        match (self, sup) {
            (Value::Builtin(b), Value::Builtin(c)) if b == c => true,
            (Value::Unit, Value::Unit) => true,
            (Value::Var(x), _) if env.ctx.vals.contains_key(x) => env.ctx.get_cloned(*x).unwrap().subtype_of(sup, env),
            (_, Value::Var(x)) if env.ctx.vals.contains_key(x) => self.subtype_of(&env.ctx.get_cloned(*x).unwrap(), env),
            (Value::Pair(ax, ay), Value::Pair(bx, by)) => ax.subtype_of(bx, env) && ay.subtype_of(by, env),
            // (Type -> (Type, Type)) <= ((Type, Type) -> Type)
            (Value::Fun(ax, ay), Value::Fun(bx, by)) => {
                if bx.subtype_of(ax, env) {
                    // Either way works, we have to check alpha equality
                    ax.match_types(bx, env);
                    ay.subtype_of(by, env)
                } else {
                    false
                }
            }
            // Two variables that haven't been resolved yet, but refer to the same definition
            (Value::Var(x), Value::Var(y)) if y == x => true,
            (_, Value::Binder(_, None)) => true,
            (Value::Binder(_, Some(t)), _) => t.subtype_of(sup, env),
            (_, Value::Binder(_, Some(t))) => self.subtype_of(t, env),
            // (Type, Type) <= Type
            (_, Value::Type) if self.is_type_type(env) => true,
            _ => false,
        }
    }
}
