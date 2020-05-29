//! Bidirectional type checking
use crate::common::*;
use crate::error::*;
use crate::eval::*;
use crate::term::*;
use std::sync::Arc;

pub type SElab = Spanned<Elab>;
type RValue = Arc<Value>;
#[derive(Debug, PartialEq, Eq)]
pub enum ElabStmt {
    Def(Spanned<Sym>, SElab),
    Expr(SElab),
}
/// Elab annotates terms with types, at least when we can't get otherwise a type easily and quickly without context
#[derive(Debug, PartialEq, Eq)]
pub enum Elab {
    Unit,                                                 // ()
    Binder(Sym, RValue),                                  // x: T
    Var(Sym, RValue),                                     // a :: T
    I32(i32),                                             // 3
    Type,                                                 // Type
    Builtin(Builtin),                                     // Int
    Fun(SElab, SElab, RValue),                            // fn a => x :: T
    App(SElab, SElab, RValue),                            // f x :: T
    Pair(SElab, SElab, RValue),                           // x, y :: T
    Struct(StructId, Vec<(Spanned<Sym>, SElab)>, RValue), // struct { x := 3 } :: T
    /// We use RawSym's here because it should work on any record with a field named this
    Project(SElab, Spanned<RawSym>, RValue), // r.m
    Block(Vec<ElabStmt>),                                 // do { x; y }
}
impl SElab {
    pub fn get_type(&self) -> RValue {
        match &**self {
            Elab::Unit => Arc::new(Value::Unit),
            Elab::Binder(_, t) => t.clone(),
            Elab::Var(_, t) => t.clone(),
            Elab::I32(_) => Arc::new(Value::Builtin(Builtin::Int)),
            Elab::Type => Arc::new(Value::Type),
            Elab::Builtin(Builtin::Int) => Arc::new(Value::Type),
            Elab::Fun(_, _, t) => t.clone(),
            Elab::App(_, _, t) => t.clone(),
            Elab::Pair(_, _, t) => t.clone(),
            Elab::Struct(_, _, t) => t.clone(),
            Elab::Project(_, _, t) => t.clone(),
            Elab::Block(x) => match x.last().unwrap() {
                ElabStmt::Def(_, _) => Arc::new(Value::Unit),
                ElabStmt::Expr(e) => e.get_type(),
            },
        }
    }
}

/// An error produced in type checking
#[derive(Debug, PartialEq, Eq)]
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
    /// Something that isn't a type was used as a type
    NotType(Spanned<Value>),
    /// We couldn't find a type for the given variable
    /// Currently, this only occurs when using bindings without a type, where we couldn't infer the type
    NotFound(Spanned<Sym>),
    /// We tried to access this field, but it's not there
    NoSuchField(Spanned<RawSym>, Value),
    /// We tried to define a field twice in a struct
    DuplicateField(Spanned<RawSym>, Spanned<RawSym>),
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
                format!("Type error: Not a function type: '{}'", WithContext(b, &*t)),
                t.span(),
                "Not a function",
            ),
            TypeError::NotType(t) => Error::new(
                file,
                format!("Type error: Not a type: '{}'", WithContext(b, &*t)),
                t.span(),
                "This was used as a type",
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
            TypeError::NoSuchField(s, v) => Error::new(
                file,
                format!(
                    "Type error: no such field '{}' on struct type '{}'",
                    b.resolve_raw(*s),
                    WithContext(b, &v),
                ),
                s.span(),
                format!("no such field"),
            ),
            TypeError::DuplicateField(x, y) => Error::new(
                file,
                format!("Type error: duplicate struct field '{}'", b.resolve_raw(*x),),
                x.span(),
                format!("first defined here"),
            )
            .with_label(file, y.span(), format!("redefined here")),
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
            TypeError::NotType(t) => write!(f, "Not a type: '{}'", WithContext(b, &**t)),
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
            TypeError::NoSuchField(s, v) => write!(
                f,
                "Type error: no such field '{}' on struct type '{}'",
                b.resolve_raw(**s),
                WithContext(b, &*v),
            ),
            TypeError::DuplicateField(x, _y) => write!(
                f,
                "Type error: duplicate struct field '{}'",
                b.resolve_raw(**x),
            ),
        }
    }
}

pub fn synth(t: &STerm, db: &impl MainGroup, env: &mut TempEnv) -> Result<SElab, TypeError> {
    #[cfg(feature = "logging")]
    println!("synth ({})", WithContext(&env.bindings(), &**t));

    match &**t {
        Term::Type => Ok(t.copy_span(Elab::Type)),
        Term::Builtin(b) => Ok(t.copy_span(Elab::Builtin(*b))),
        Term::Var(x) => {
            let ty = db
                .elab(env.scope.clone(), *x)
                .map(|x| x.get_type())
                .or_else(|| env.ty(*x))
                .map(|x| x.cloned(&mut env.clone()))
                .ok_or_else(|| TypeError::NotFound(t.copy_span(*x)))?;
            Ok(t.copy_span(Elab::Var(*x, Arc::new(ty))))
        }
        Term::I32(i) => Ok(t.copy_span(Elab::I32(*i))),
        Term::Unit => Ok(t.copy_span(Elab::Unit)),
        Term::Pair(x, y) => {
            // TODO I don't think this covers dependent pairs
            let x = synth(x, db, env)?;
            let y = synth(y, db, env)?;
            let ty = Arc::new(Value::Pair(
                Box::new(x.get_type().cloned(&mut env.clone())),
                Box::new(x.get_type().cloned(&mut env.clone())),
            ));
            Ok(t.copy_span(Elab::Pair(x, y, ty)))
        }
        Term::Struct(id, iv) => {
            let mut rv = Vec::new();
            let mut syms: Vec<Spanned<Sym>> = Vec::new();
            let mut tv = Vec::new();
            let mut env = env.child(*id);
            for (name, val) in iv {
                if let Some(n2) = syms.iter().find(|n| n.raw() == name.raw()) {
                    return Err(TypeError::DuplicateField(
                        n2.copy_span(n2.raw()),
                        name.copy_span(name.raw()),
                    ));
                }
                syms.push(name.clone());

                let e = synth(val, db, &mut env)?;
                tv.push((**name, e.get_type().cloned(&mut env)));
                rv.push((name.clone(), e));
            }
            Ok(t.copy_span(Elab::Struct(*id, rv, Arc::new(Value::Struct(tv)))))
        }
        Term::App(f, x) => {
            let f = synth(f, db, env)?;
            let (ret, x) = match &*f.get_type() {
                Value::Fun(from, to) => {
                    let x2 = check(x, &from, db, env)?;
                    // Stick the value in in case it's dependent
                    let mut to = to.cloned(&mut env.clone());
                    let x = x.reduce(db, env);
                    from.do_match(&x, env);
                    to.update(env);
                    (to, x2)
                }
                a => return Err(TypeError::NotFunction(f.copy_span(a.cloned(&mut env.clone())))),
            };
            Ok(t.copy_span(Elab::App(f, x, Arc::new(ret))))
        }
        Term::Project(r, m) => {
            let r = synth(r, db, env)?;
            let rt = r.get_type();
            let rt = match &*rt {
                Value::Struct(v) => {
                    if let Some((_, val)) = v.iter().find(|(name, _)| name.raw() == **m) {
                        val.cloned(&mut env.clone())
                    } else {
                        return Err(TypeError::NoSuchField(m.clone(), rt.cloned(&mut env.clone())));
                    }
                }
                _ => return Err(TypeError::NoSuchField(m.clone(), rt.cloned(&mut env.clone()))),
            };
            Ok(t.copy_span(Elab::Project(r, m.clone(), Arc::new(rt))))
        }
        Term::Fun(x, y) => {
            // Make sure it's well typed before reducing it
            let xe = check(x, &Value::Type, db, env)?;
            let xv = x.reduce(db, env);
            // Match it with itself to apply the types
            xv.match_types(&xv, env);
            let y = synth(y, db, env)?;
            let ty = Arc::new(Value::Fun(
                Box::new(xe.get_type().cloned(&mut env.clone())),
                Box::new(y.get_type().cloned(&mut env.clone())),
            ));
            Ok(t.copy_span(Elab::Fun(xe, y, ty)))
        }
        Term::Block(v) => {
            let mut rv = Vec::new();
            for i in 0..v.len() {
                match &v[i] {
                    Statement::Expr(t) => {
                        if i + 1 != v.len() {
                            rv.push(ElabStmt::Expr(check(t, &Value::Unit, db, env)?));
                        } else {
                            // last value
                            rv.push(ElabStmt::Expr(synth(t, db, env)?));
                        }
                    }
                    Statement::Def(Def(name, val)) => {
                        let ve = synth(val, db, env)?;
                        env.arc_ty(**name, ve.get_type());
                        // Blocks can be dependent!
                        let val = val.reduce(db, env);
                        env.set_val(**name, val);
                        rv.push(ElabStmt::Def(name.clone(), ve));
                    }
                }
            }
            Ok(t.copy_span(Elab::Block(rv)))
        }
        Term::The(ty, u) => {
            // Make sure it's well typed before reducing it
            let _ = check(ty, &Value::Type, db, env)?;
            let ty = ty.reduce(db, env);
            let ue = check(u, &ty, db, env)?;
            Ok(ue)
        }
        Term::Binder(_, Some(t)) => synth(t, db, env),
        _ => Err(TypeError::Synth(t.clone())),
    }
}

/// Checks the given term against the given type
pub fn check(
    term: &STerm,
    typ: &Value,
    db: &impl MainGroup,
    env: &mut TempEnv,
) -> Result<SElab, TypeError> {
    #[cfg(feature = "logging")]
    {
        let b = &env.bindings();
        println!(
            "check ({}) :: ({})",
            WithContext(b, &**term),
            WithContext(b, typ)
        );
    }

    match (&**term, typ) {
        (Term::Binder(s, Some(t)), _) => {
            let _ = check(t, typ, db, env)?;
            let t = t.reduce(db, env);
            Ok(term.copy_span(Elab::Binder(*s, Arc::new(t))))
        }

        (Term::Pair(x, y), Value::Pair(tx, ty)) => {
            // TODO dependent pairs don't really work
            check(x, tx, db, env)?;
            check(y, ty, db, env)
        }

        // As far as we know, it could be any type
        (Term::Binder(s, None), _) if typ.subtype_of(&Value::Type, &mut env.clone()) => Ok(term.copy_span(Elab::Binder(
            *s, Arc::new(typ.cloned(&mut env.clone()))
        ))),

        (Term::Fun(x, b), Value::Fun(y, to)) => {
            // Make sure it's well typed before reducing it
            let xe = check(x, &Value::Type, db, env)?;
            let xr = x.reduce(db, env);
            // Because patterns are types, match checking amounts to subtype checking
            if y.subtype_of(&xr, &mut env.clone()) {
                xr.match_types(y, env);
                let be = check(b, to, db, env)?;
                Ok(term.copy_span(Elab::Fun(xe, be, Arc::new(typ.cloned(&mut env.clone())))))
            } else {
                Err(TypeError::NotSubtypeF(
                    y.cloned(&mut env.clone()),
                    x.copy_span(xr),
                ))
            }
        }
        (_, Value::Type) => {
            let t = synth(term, db, env)?;
            let ty = t.get_type();
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&Value::Type, &mut env.clone()) {
                Ok(t)
            } else {
                Err(TypeError::NotType(term.copy_span(ty.cloned(&mut env.clone()))))
            }
        }
        (_, _) => {
            let t = synth(term, db, env)?;
            let ty = t.get_type();
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&typ, &mut env.clone()) {
                Ok(t)
            } else {
                Err(TypeError::NotSubtype(
                    term.copy_span(ty.cloned(&mut env.clone())),
                    typ.cloned(&mut env.clone()),
                ))
            }
        }
    }
}

impl Value {
    /// Like do_match(), but fills in the types instead of values
    fn match_types(&self, other: &Value, env: &mut TempEnv) {
        use Value::*;
        match (self, other) {
            // Since we match it against itself to apply binder types
            (Binder(na, _), Binder(nb, t)) if na == nb => {
                if let Some(t) = t {
                    #[cfg(feature = "logging")]
                    {
                        let b = &env.bindings();
                        println!("env: {} : {}", WithContext(b, self), WithContext(b, &**t));
                    }

                    let t = t.cloned(&mut env.clone());
                    env.set_ty(*na, t);
                }
            }
            // For alpha-equivalence - we need symbols in our body to match symbols in the other body if they're defined as the same
            (_, Binder(x, t)) => {
                self.do_match(&Var(*x), env);
                if let Some(t) = t {
                    self.match_types(t, env);
                }
            }
            (Binder(s, _), _) => {
                #[cfg(feature = "logging")]
                {
                    let b = &env.bindings();
                    println!("type: {} : {}", WithContext(b, self), WithContext(b, other));
                }

                let other = other.cloned(&mut env.clone());
                env.set_ty(*s, other);
            }
            (Var(x), _) => {
                if let Some(x) = env.val(*x) {
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
            Value::Struct(v) => v.iter().all(|(_, x)| x.is_type()),
            Value::Binder(_, _) => true,
            // We're not sure, but it could be
            Value::Var(_) => true,
            _ => false,
        }
    }

    /// Is this a subtype of Type?
    fn is_type_type(&self) -> bool {
        match self {
            Value::Type => true,
            Value::Pair(x, y) => x.is_type_type() && y.is_type_type(),
            Value::Fun(_, x) => x.is_type_type(),
            Value::Binder(_, None) => true,
            Value::Binder(_, Some(t)) => t.is_type_type(),
            _ => false,
        }
    }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality
    pub fn subtype_of(&self, sup: &Value, env: &mut TempEnv) -> bool {
        if !self.is_type() {
            return false;
        }
        match (self, sup) {
            (Value::Struct(sub), Value::Struct(sup)) => {
                // We DON'T do record subtyping, that's hard to compile efficiently
                sup.iter().all(|(n, sup)| sub.iter().find(|(n2, _)| n2.raw() == n.raw()).map_or(false, |(_, sub)| sub.subtype_of(sup, env)))
                // so make sure there aren't any extra fields
                    && sub.iter().all(|(n, _)| sup.iter().any(|(n2, _)| n2.raw() == n.raw()))
            }
            (Value::Builtin(b), Value::Builtin(c)) if b == c => true,
            (Value::Unit, Value::Unit) => true,
            (Value::Var(x), _) if env.vals.contains_key(x) => {
                env.val(*x).unwrap().cloned(env).subtype_of(sup, env)
            }
            (_, Value::Var(x)) if env.vals.contains_key(x) => {
                self.subtype_of(&env.val(*x).unwrap().cloned(env), env)
            }
            (Value::Pair(ax, ay), Value::Pair(bx, by)) => {
                ax.subtype_of(bx, env) && ay.subtype_of(by, env)
            }
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
            (_, Value::Type) if self.is_type_type() => true,
            _ => false,
        }
    }
}
