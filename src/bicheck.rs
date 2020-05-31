//! Bidirectional type checking
use crate::common::*;
use crate::error::*;
use crate::elab::*;
use crate::term::*;
use std::sync::Arc;

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum ElabStmt {
//     Def(Spanned<Sym>, SElab),
//     Expr(SElab),
// }
// /// Elab annotates terms with types, at least when we can't get otherwise a type easily and quickly without context
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum Elab {
//     Unit,                                                 // ()
//     Binder(Sym, RElab),                                  // x: T
//     Var(Sym, RElab),                                     // a :: T
//     I32(i32),                                             // 3
//     Type,                                                 // Type
//     Builtin(Builtin),                                     // Int
//     Fun(SElab, SElab, RElab),                            // fn a => x :: T
//     App(SElab, SElab, RElab),                            // f x :: T
//     Pair(SElab, SElab, RElab),                           // x, y :: T
//     Struct(StructId, Vec<(Spanned<Sym>, SElab)>, RElab), // struct { x := 3 } :: T
//     /// We use RawSym's here because it should work on any record with a field named this
//     Project(SElab, Spanned<RawSym>, RElab), // r.m
//     Block(Vec<ElabStmt>),                                 // do { x; y }
// }
// impl CDisplay for Elab {
//     fn fmt(&self, f: &mut std::fmt::Formatter, b: &Bindings) -> std::fmt::Result {
//         match self {
//             Elab::Unit => write!(f, "()"),
//             Elab::Binder(x, t) => {
//                 write!(f, "{}{}: {}", b.resolve(*x), x.num(), WithContext(b, &**t))
//             }
//             Elab::Var(s, t) => write!(f, "({}{} :: {})", b.resolve(*s), s.num(), WithContext(b, &**t)),
//             Elab::I32(i) => write!(f, "{}", i),
//             Elab::Type => write!(f, "Type"),
//             Elab::Builtin(b) => write!(f, "{:?}", b),
//             Elab::Fun(x, y, _) => write!(
//                 f,
//                 "fun {} => {}",
//                 WithContext(b, &**x),
//                 WithContext(b, &**y)
//             ),
//             Elab::App(x, y, _) => write!(f, "{}({})", WithContext(b, &**x), WithContext(b, &**y)),
//             Elab::Pair(x, y, _) => write!(f, "({}, {})", WithContext(b, &**x), WithContext(b, &**y)),
//             Elab::Struct(id, v, _) => {
//                 write!(f, "struct({}) {{ ", id.num())?;
//                 for (name, val) in v.iter() {
//                     write!(
//                         f,
//                         "{}{} := {}, ",
//                         b.resolve(**name),
//                         name.num(),
//                         WithContext(b, &**val)
//                     )?;
//                 }
//                 write!(f, "}}")
//             }
//             Elab::Block(v) => {
//                 write!(f, "do {{ ")?;
//                 for s in v.iter() {
//                     match s {
//                         ElabStmt::Expr(e) => write!(f, "{}; ", WithContext(b, &**e)),
//                         ElabStmt::Def(name, val) => write!(
//                             f,
//                             "{}{} := {}; ",
//                             b.resolve(**name),
//                             name.num(),
//                             WithContext(b, &**val)
//                         ),
//                     }?;
//                 }
//                 write!(f, "}}")
//             }
//             Elab::Project(r, m, _) => write!(f, "({}).{}", WithContext(b, &**r), b.resolve_raw(**m),),
//         }
//     }
// }
// impl SElab {
//     /// Evaluate a `Term` into its `Elab` representation (i.e. normal form), given a context
//     ///
//     /// Note that this function can accept, and reduce, ill-typed terms, so always typecheck a `Term` before reducing it
//     pub fn reduce(&self, db: &impl MainGroup, env: &mut TempEnv) -> Elab {
//         match &**self {
//             Elab::Unit => Elab::Unit,
//             Elab::I32(i) => Elab::I32(*i),
//             Elab::Type => Elab::Type,
//             Elab::Builtin(b) => Elab::Builtin(*b),
//             Elab::Var(s, _) => match db.val(env.scope.clone(), *s).or_else(|| env.val(*s)) {
//                 Some(x) => x.cloned(&mut env.clone()),
//                 // Free variable
//                 None => Elab::Var(*s),
//             },
//             Elab::Binder(s, t) => {
//                 Elab::Binder(*s, Box::new(t.cloned(&mut env.clone())))
//             }
//             Elab::Pair(x, y, _) => {
//                 Elab::Pair(Box::new(x.reduce(db, env)), Box::new(y.reduce(db, env)))
//             }
//             Elab::Fun(x, y, _) => Elab::Fun(Box::new(x.reduce(db, env)), Box::new(y.reduce(db, env))),
//             Elab::App(f, x, _) => {
//                 let f = f.reduce(db, env);
//                 let x = x.reduce(db, env);
//                 match f {
//                     Elab::Fun(args, mut body) => {
//                         args.do_match(&x, env);
//                         body.update(env);
//                         *body
//                     }
//                     // Neutral - we can't apply it yet
//                     f => Elab::App(Box::new(f), Box::new(x)),
//                 }
//             }
//             Elab::Struct(id, v, _) => Elab::Struct(*id, {
//                 let mut env = env.child(*id);
//                 v.iter()
//                     .map(|(name, val)| (**name, val.reduce(db, &mut env)))
//                     .collect()
//             }),
//             Elab::Project(r, m, _) => {
//                 let r = r.reduce(db, env);
//                 match r {
//                     Elab::Struct(_, v) => {
//                         // We unwrap because this type checked already
//                         let (_, val) = v.iter().find(|(name, _)| name.raw() == **m).unwrap();
//                         val.cloned(&mut env.clone())
//                     }
//                     // Not a record yet, we can't project it
//                     r => Elab::Project(Box::new(r), **m),
//                 }
//             }
//             Elab::Block(v) => {
//                 for i in 0..v.len() {
//                     match &v[i] {
//                         // Expressions currently can't do anything in this position
//                         ElabStmt::Expr(e) => {
//                             if i + 1 == v.len() {
//                                 return e.reduce(db, env);
//                             } else {
//                             }
//                         }
//                         ElabStmt::Def(name, val) => {
//                             let val = val.reduce(db, env);
//                             env.set_val(**name, val);
//                         }
//                     }
//                 }
//                 Elab::Unit
//             }
//         }
//     }
//
//     /// It's possible the returned term won't actually typecheck, since we lost type information
//     /// However, it should still be well-typed
//     pub fn as_term(&self) -> STerm {
//         self.copy_span(match &**self {
//             Elab::Unit => Term::Unit,
//             Elab::Binder(s, t) => Term::Binder(*s, None),
//             _ => panic!()
//         })
//     }
//
//     pub fn monomorphize(&self, ty: &Elab, env: &mut TempEnv) -> Self {
//         self.copy_span(match &**self {
//             Elab::Unit => Elab::Unit,
//             Elab::Binder(s, _) => Elab::Binder(*s, Arc::new(ty.cloned(env))),
//             Elab::Var(s, _) => Elab::Var(*s, Arc::new(ty.cloned(env))),
//             Elab::I32(i) => Elab::I32(*i),
//             Elab::Type => Elab::Type,
//             Elab::Builtin(b) => Elab::Builtin(*b),
//             Elab::Fun(a, b, _) => if let Elab::Fun(from, to) = ty
//                 {
//                     Elab::Fun(a.monomorphize(from, env), b.monomorphize(to, env), Arc::new(ty.cloned(env)))
//                 } else { panic!("Monomorphizing a function to a non-function type: {}!", WithContext(&env.bindings(), ty)) }
//             Elab::App(a, b, _) => if let Elab::Fun(from, _) = &*a.get_type() { Elab::App(
//                 a.monomorphize(&Elab::Fun(Box::new(from.cloned(env)), Box::new(ty.cloned(env))), env),
//                 b.monomorphize(ty, env),
//                 Arc::new(ty.cloned(env)),
//             ) } else { unreachable!() }
//             Elab::Pair(a, b, _) => if let Elab::Pair(at, bt) = ty
//                 {
//                     Elab::Pair(a.monomorphize(at, env), b.monomorphize(bt, env), Arc::new(ty.cloned(env)))
//                 } else { panic!("Monomorphizing a pair to a non-pair type: {}!", WithContext(&env.bindings(), ty)) }
//             // TODO recurse in these three
//             Elab::Struct(a, b, _) => Elab::Struct(a.clone(), b.clone(), Arc::new(ty.cloned(env))),
//             Elab::Project(r, m, _) => Elab::Project(r.clone(), m.clone(), Arc::new(ty.cloned(env))),
//             Elab::Block(v) => Elab::Block(v.clone()),
//         })
//     }
//
//     pub fn get_type(&self) -> RElab {
//         match &**self {
//             Elab::Unit => Arc::new(Elab::Unit),
//             Elab::Binder(_, _) => Arc::new(Elab::Type),//t.clone(),
//             Elab::Var(_, t) => t.clone(),
//             Elab::I32(_) => Arc::new(Elab::Builtin(Builtin::Int)),
//             Elab::Type => Arc::new(Elab::Type),
//             Elab::Builtin(Builtin::Int) => Arc::new(Elab::Type),
//             Elab::Fun(_, _, t) => t.clone(),
//             Elab::App(_, _, t) => t.clone(),
//             Elab::Pair(_, _, t) => t.clone(),
//             Elab::Struct(_, _, t) => t.clone(),
//             Elab::Project(_, _, t) => t.clone(),
//             Elab::Block(x) => match x.last().unwrap() {
//                 ElabStmt::Def(_, _) => Arc::new(Elab::Unit),
//                 ElabStmt::Expr(e) => e.get_type(),
//             },
//         }
//     }
// }

/// An error produced in type checking
#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    /// We couldn't synthesize a type for the given term
    Synth(STerm),
    /// We tried to apply the given term, but it's not a function
    /// The `Elab` here is the type
    NotFunction(Spanned<Elab>),
    /// The first Elab needs to be a subtype of the second one, but it's not
    NotSubtype(Spanned<Elab>, Elab),
    /// `NotSubtype` with flipped span information
    NotSubtypeF(Elab, Spanned<Elab>),
    /// Something that isn't a type was used as a type
    NotType(Spanned<Elab>),
    /// We couldn't find a type for the given variable
    /// Currently, this only occurs when using bindings without a type, where we couldn't infer the type
    NotFound(Spanned<Sym>),
    /// We tried to access this field, but it's not there
    NoSuchField(Spanned<RawSym>, Elab),
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

/// Attempts to come up with a type for a term, returning the elaborated term
pub fn synth(t: &STerm, db: &impl MainGroup, env: &mut TempEnv) -> Result<Elab, TypeError> {
    #[cfg(feature = "logging")]
    println!("synth ({})", WithContext(&env.bindings(), &**t));

    match &**t {
        Term::Type => Ok(Elab::Type),
        Term::Builtin(b) => Ok(Elab::Builtin(*b)),
        Term::Var(x) => {
            let ty = db
                .elab(env.scope.clone(), *x)
                .map(|x| x.get_type(env))
                .or_else(|| env.ty(*x).map(|x|x.cloned(&mut env.clone())))
                .ok_or_else(|| TypeError::NotFound(t.copy_span(*x)))?;
            Ok(Elab::Var(*x, Box::new(ty)))
        }
        Term::I32(i) => Ok(Elab::I32(*i)),
        Term::Unit => Ok(Elab::Unit),
        Term::Pair(x, y) => {
            // TODO I don't think this covers dependent pairs
            let x = synth(x, db, env)?;
            let y = synth(y, db, env)?;
            Ok(Elab::Pair(Box::new(x), Box::new(y)))
        }
        Term::Struct(id, iv) => {
            let mut rv = Vec::new();
            let mut syms: Vec<Spanned<Sym>> = Vec::new();
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
                rv.push((**name, e));
            }
            Ok(Elab::Struct(*id, rv))
        }
        Term::App(fi, x) => {
            let f = synth(fi, db, env)?;
            let (ret, x) = match f.get_type(env) {
                Elab::Fun(from, to, _) => {
                    let x = check(x, &from, db, env)?;
                    // Stick the Elab in in case it's dependent
                    // let x = x2.reduce(db, env);
                    from.do_match(&x, env);
                    let to = to.cloned(&mut env.clone());
                    // println!("F is: {}", WithContext(&env.bindings(), &*f));
                    // println!("X is: {}", WithContext(&env.bindings(), &x));
                    // println!("Before match: {}", WithContext(&env.bindings(), &to));
                    // to.update(env);
                    // println!("After match:  {}", WithContext(&env.bindings(), &to));
                    (to, x)
                }
                a => return Err(TypeError::NotFunction(fi.copy_span(a.cloned(&mut env.clone())))),
            };
            // println!("Unmorphized: {}", WithContext(&env.bindings(), &*f));
            // let f = f.monomorphize(&Elab::Fun(Box::new(x.get_type().cloned(&mut env.clone())), Box::new(ret.cloned(&mut env.clone()))), &mut env.clone());
            // println!("Morphized: {}", WithContext(&env.bindings(), &*f));
            Ok(Elab::App(Box::new(f), Box::new(x)))
        }
        Term::Project(r, m) => {
            let r = synth(r, db, env)?;
            let rt = r.get_type(env);
            let rt = match &rt {
                Elab::Struct(_, v) => {
                    if let Some((_, val)) = v.iter().find(|(name, _)| name.raw() == **m) {
                        val.cloned(&mut env.clone())
                    } else {
                        return Err(TypeError::NoSuchField(m.clone(), rt.cloned(&mut env.clone())));
                    }
                }
                _ => return Err(TypeError::NoSuchField(m.clone(), rt.cloned(&mut env.clone()))),
            };
            Ok(Elab::Project(Box::new(r), **m))
        }
        Term::Fun(x, y) => {
            // Make sure it's well typed before reducing it
            let x = check(x, &Elab::Type, db, env)?;
            // let xv = xe.reduce(db, env);
            // Match it with itself to apply the types
            x.match_types(&x, env);
            let y = synth(y, db, env)?;
            let to = y.get_type(env);
            Ok(Elab::Fun(Box::new(x), Box::new(y), Box::new(to)))
        }
        Term::Block(v) => {
            let mut rv = Vec::new();
            for i in 0..v.len() {
                match &v[i] {
                    Statement::Expr(t) => {
                        if i + 1 != v.len() {
                            rv.push(ElabStmt::Expr(check(t, &Elab::Unit, db, env)?));
                        } else {
                            // last Elab
                            rv.push(ElabStmt::Expr(synth(t, db, env)?));
                        }
                    }
                    Statement::Def(Def(name, val)) => {
                        let val = synth(val, db, env)?;
                        let ty = val.get_type(env);
                        env.set_ty(**name, ty);
                        // Blocks can be dependent!
                        // let val = ve.reduce(db, env);
                        env.set_val(**name, val.cloned(&mut env.clone()));
                        rv.push(ElabStmt::Def(**name, val));
                    }
                }
            }
            Ok(Elab::Block(rv))
        }
        Term::The(ty, u) => {
            // Make sure it's well typed before reducing it
            let ty = check(ty, &Elab::Type, db, env)?;
            // let ty = ty.reduce(db, env);
            let ue = check(u, &ty, db, env)?;
            Ok(ue)
        }
        Term::Binder(x, Some(ty)) => {
            let ty = check(ty, &Elab::Type, db, env)?;
            // let ty = ty.reduce(db, env);
            Ok(Elab::Binder(*x, Box::new(ty)))
        }
        _ => Err(TypeError::Synth(t.clone())),
    }
}

/// Checks the given term against the given type, returning the elaborated term
pub fn check(
    term: &STerm,
    typ: &Elab,
    db: &impl MainGroup,
    env: &mut TempEnv,
) -> Result<Elab, TypeError> {
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
        (Term::Pair(x, y), Elab::Pair(tx, ty)) => {
            // TODO dependent pairs don't really work
            check(x, tx, db, env)?;
            check(y, ty, db, env)
        }

        // As far as we know, it could be any type
        (Term::Binder(s, None), _) if typ.subtype_of(&Elab::Type, &mut env.clone()) => Ok(Elab::Binder(
            *s, Box::new(typ.cloned(&mut env.clone()))
        )),

        (Term::Fun(x, b), Elab::Fun(y, to, _)) => {
            // Make sure it's well typed before reducing it
            let xr = check(x, &Elab::Type, db, env)?;
            // let xr = xe.reduce(db, env);
            // Because patterns are types, match checking amounts to subtype checking
            if y.subtype_of(&xr, &mut env.clone()) {
                // let xe = xe.monomorphize(y, &mut env.clone());
                xr.match_types(y, env);
                let be = check(b, to, db, env)?;//.monomorphize(to, &mut env.clone());
                Ok(Elab::Fun(Box::new(xr), Box::new(be), Box::new(to.cloned(&mut env.clone()))))
            } else {
                Err(TypeError::NotSubtypeF(
                    y.cloned(&mut env.clone()),
                    x.copy_span(xr),
                ))
            }
        }
        (_, Elab::Type) => {
            let t = synth(term, db, env)?;
            let ty = t.get_type(env);
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&Elab::Type, &mut env.clone()) {
                Ok(t)
            } else {
                Err(TypeError::NotType(term.copy_span(ty.cloned(&mut env.clone()))))
            }
        }
        (_, _) => {
            let t = synth(term, db, env)?;
            let ty = t.get_type(env);
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&typ, &mut env.clone()) {
                Ok(t)//.monomorphize(&typ, &mut env.clone()))
            } else {
                Err(TypeError::NotSubtype(
                    term.copy_span(ty.cloned(&mut env.clone())),
                    typ.cloned(&mut env.clone()),
                ))
            }
        }
    }
}

impl Elab {
    /// Like do_match(), but fills in the types instead of Elabs
    fn match_types(&self, other: &Elab, env: &mut TempEnv) {
        use Elab::*;
        match (self, other) {
            // Since we match it against itself to apply binder types
            (Binder(na, _), Binder(nb, t)) if na == nb => {
                #[cfg(feature = "logging")]
                {
                    let b = &env.bindings();
                    println!("env: {} : {}", WithContext(b, self), WithContext(b, &**t));
                }

                let t = t.cloned(&mut env.clone());
                env.set_ty(*na, t);
            }
            // For alpha-equivalence - we need symbols in our body to match symbols in the other body if they're defined as the same
            (_, Binder(x, t)) => {
                self.do_match(&Var(*x, Box::new(t.cloned(&mut env.clone()))), env);
                self.match_types(t, env);
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
            (Var(x, _), _) => {
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
            Elab::Type | Elab::Unit | Elab::Builtin(Builtin::Int) => true,
            Elab::Fun(_, x, _) => x.is_type(),
            Elab::Pair(x, y) => x.is_type() && y.is_type(),
            Elab::Struct(_, v) => v.iter().all(|(_, x)| x.is_type()),
            Elab::Binder(_, _) => true,
            Elab::Var(_, t) => t.is_type_type(),
            _ => false,
        }
    }

    /// Is this a subtype of Type?
    fn is_type_type(&self) -> bool {
        match self {
            // () : () : ()
            Elab::Unit => true,
            Elab::Type => true,
            Elab::Pair(x, y) => x.is_type_type() && y.is_type_type(),
            Elab::Fun(_, x, _) => x.is_type_type(),
            Elab::Binder(_, t) => t.is_type_type(),
            Elab::Var(_, t) => t.is_type_type(),
            _ => false,
        }
    }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality
    pub fn subtype_of(&self, sup: &Elab, env: &mut TempEnv) -> bool {
        if !self.is_type() {
            return false;
        }
        match (self, sup) {
            (Elab::Struct(_, sub), Elab::Struct(_, sup)) => {
                // We DON'T do record subtyping, that's hard to compile efficiently
                sup.iter().all(|(n, sup)| sub.iter().find(|(n2, _)| n2.raw() == n.raw()).map_or(false, |(_, sub)| sub.subtype_of(sup, env)))
                // so make sure there aren't any extra fields
                    && sub.iter().all(|(n, _)| sup.iter().any(|(n2, _)| n2.raw() == n.raw()))
            }
            (Elab::Builtin(b), Elab::Builtin(c)) if b == c => true,
            (Elab::Unit, Elab::Unit) => true,
            (Elab::Var(x, _), _) if env.vals.contains_key(x) => {
                env.val(*x).unwrap().cloned(env).subtype_of(sup, env)
            }
            (_, Elab::Var(x, _)) if env.vals.contains_key(x) => {
                self.subtype_of(&env.val(*x).unwrap().cloned(env), env)
            }
            (Elab::Pair(ax, ay), Elab::Pair(bx, by)) => {
                ax.subtype_of(bx, env) && ay.subtype_of(by, env)
            }
            // (Type -> (Type, Type)) <= ((Type, Type) -> Type)
            (Elab::Fun(ax, ay, _), Elab::Fun(bx, by, _)) => {
                if bx.subtype_of(ax, env) {
                    // Either way works, we have to check alpha equality
                    ax.match_types(bx, env);
                    ay.subtype_of(by, env)
                } else {
                    false
                }
            }
            // Two variables that haven't been resolved yet, but refer to the same definition
            (Elab::Var(x, _), Elab::Var(y, _)) if y == x => true,
            (Elab::Binder(_, t), _) => t.subtype_of(sup, env),
            (_, Elab::Binder(_, t)) => self.subtype_of(t, env),
            // (Type, Type) <= Type
            (_, Elab::Type) if self.is_type_type() => true,
            _ => false,
        }
    }
}
