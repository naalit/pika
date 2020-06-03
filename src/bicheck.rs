//! Bidirectional type checking
use crate::common::*;
use crate::elab::*;
use crate::error::*;
use crate::term::*;

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
                Doc::start("Type error: could not synthesize type for '")
                    .chain(t.pretty(b).style(Style::None))
                    .add("': try adding an annotation")
                    .style(Style::Bold),
                t.span(),
                "try adding an annotation here",
            ),
            TypeError::NotFunction(t) => Error::new(
                file,
                Doc::start("Type error: not a function: '")
                    .chain(t.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                t.span(),
                "Not a function",
            ),
            TypeError::NotType(t) => Error::new(
                file,
                Doc::start("Type error: not a type: '")
                    .chain(t.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                t.span(),
                "This was used as a type",
            ),
            TypeError::NotSubtype(sub, sup) => Error::new(
                file,
                Doc::start("Type error: could not match types '")
                    .chain(sub.pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(sup.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                sub.span(),
                Doc::start("this has type '")
                    .chain(sub.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::NotSubtypeF(sub, sup) => Error::new(
                file,
                Doc::start("Type error: could not match types '")
                    .chain(sub.pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(sup.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                sup.span(),
                Doc::start("this has type '")
                    .chain(sup.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::NotFound(s) => Error::new(
                file,
                Doc::start("Type error: could not find type for variable: '")
                    .chain(s.pretty(b))
                    .add("'")
                    .style(Style::Bold),
                s.span(),
                format!("type not found"),
            ),
            TypeError::NoSuchField(s, v) => Error::new(
                file,
                Doc::start("Type error: no such field '")
                    .chain(s.pretty(b))
                    .add("' on struct type '")
                    .chain(v.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                s.span(),
                format!("no such field"),
            ),
            TypeError::DuplicateField(x, y) => Error::new(
                file,
                Doc::start("Type error: could not find type for variable: '")
                    .chain(x.pretty(b))
                    .add("'")
                    .style(Style::Bold),
                x.span(),
                format!("first defined here"),
            )
            .with_label(file, y.span(), format!("redefined here")),
        }
    }
}

/// Attempts to come up with a type for a term, returning the elaborated term
pub fn synth<T: MainGroup>(t: &STerm, env: &mut TempEnv<T>) -> Result<Elab, TypeError> {
    #[cfg(feature = "logging")]
    println!("synth ({})", t.pretty(&*env.bindings()).ansi_string());

    match &**t {
        Term::Type => Ok(Elab::Type),
        Term::Builtin(b) => Ok(Elab::Builtin(*b)),
        Term::Var(x) => {
            let ty = env
                .db
                .elab(env.scope.clone(), *x)
                .map(|x| x.get_type(env))
                .or_else(|| env.ty(*x).map(|x| x.cloned(&mut env.clone())))
                .ok_or_else(|| TypeError::NotFound(t.copy_span(*x)))?;
            Ok(Elab::Var(*x, Box::new(ty)))
        }
        Term::I32(i) => Ok(Elab::I32(*i)),
        Term::Unit => Ok(Elab::Unit),
        Term::Pair(x, y) => {
            // TODO I don't think this covers dependent pairs
            let x = synth(x, env)?;
            let y = synth(y, env)?;
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

                let e = synth(val, &mut env)?;
                rv.push((**name, e));
            }
            Ok(Elab::Struct(*id, rv))
        }
        Term::App(fi, x) => {
            let f = synth(fi, env)?;
            let x = match f.get_type(env) {
                Elab::Fun(mut from, _, _) => {
                    from.whnf(env);
                    check(x, &from, env)?
                }
                a => {
                    return Err(TypeError::NotFunction(
                        fi.copy_span(a.cloned(&mut env.clone())),
                    ))
                }
            };
            Ok(Elab::App(Box::new(f), Box::new(x)))
        }
        Term::Project(r, m) => {
            let r = synth(r, env)?;
            let rt = r.get_type(env);
            match &r.get_type(env) {
                Elab::Struct(_, v) => {
                    if let Some((_, val)) = v.iter().find(|(name, _)| name.raw() == **m) {
                        val.cloned(&mut env.clone())
                    } else {
                        return Err(TypeError::NoSuchField(
                            m.clone(),
                            rt.cloned(&mut env.clone()),
                        ));
                    }
                }
                _ => {
                    return Err(TypeError::NoSuchField(
                        m.clone(),
                        rt.cloned(&mut env.clone()),
                    ))
                }
            };
            Ok(Elab::Project(Box::new(r), **m))
        }
        Term::Fun(x, y) => {
            // Make sure it's well typed before reducing it
            let mut x = check(x, &Elab::Type, env)?;
            x.whnf(env);
            // Match it with itself to apply the types
            x.match_types(&x, env);
            let y = synth(y, env)?;
            let mut to = y.get_type(env);
            to.whnf(env);
            Ok(Elab::Fun(Box::new(x), Box::new(y), Box::new(to)))
        }
        Term::Block(v) => {
            let mut rv = Vec::new();
            for i in 0..v.len() {
                match &v[i] {
                    Statement::Expr(t) => {
                        if i + 1 != v.len() {
                            rv.push(ElabStmt::Expr(check(t, &Elab::Unit, env)?));
                        } else {
                            // last value
                            rv.push(ElabStmt::Expr(synth(t, env)?));
                        }
                    }
                    Statement::Def(Def(name, val)) => {
                        let mut val = synth(val, env)?;
                        let ty = val.get_type(env);
                        env.set_ty(**name, ty);
                        // Blocks can be dependent!
                        val.whnf(env);
                        env.set_val(**name, val.cloned(&mut env.clone()));
                        rv.push(ElabStmt::Def(**name, val));
                    }
                }
            }
            Ok(Elab::Block(rv))
        }
        Term::The(ty, u) => {
            // Make sure it's well typed before reducing it
            let mut ty = check(ty, &Elab::Type, env)?;
            ty.whnf(env);
            let ue = check(u, &ty, env)?;
            Ok(ue)
        }
        Term::Binder(x, Some(ty)) => {
            let mut ty = check(ty, &Elab::Type, env)?;
            ty.whnf(env);
            Ok(Elab::Binder(*x, Box::new(ty)))
        }
        _ => Err(TypeError::Synth(t.clone())),
    }
}

/// Checks the given term against the given type, returning the elaborated term
pub fn check<T: MainGroup>(
    term: &STerm,
    typ: &Elab,
    env: &mut TempEnv<T>,
) -> Result<Elab, TypeError> {
    #[cfg(feature = "logging")]
    {
        let b = &env.bindings();
        println!(
            "check ({}) :: ({})",
            term.pretty(b).ansi_string(),
            typ.pretty(b).ansi_string(),
        );
    }

    match (&**term, typ) {
        (Term::Pair(x, y), Elab::Pair(tx, ty)) => {
            let (mut tx, mut ty) = (tx.cloned(env), ty.cloned(env));
            tx.whnf(env);
            ty.whnf(env);
            // TODO dependent pairs don't really work
            check(x, &tx, env)?;
            check(y, &ty, env)
        }

        // As far as we know, it could be any type
        (Term::Binder(s, None), _) if typ.subtype_of(&Elab::Type, &mut env.clone()) => {
            Ok(Elab::Binder(
                // This is WRONG, because the *value* of the binder (which *is* a type but not the type of the binder) is the second parameter
                // We don't know what that is, though, so we'll probably introduce a metavariable when we have them
                // For now, we should call update_binders wherever we have the information, so this should dissapear
                *s,
                Box::new(typ.cloned(&mut env.clone())),
            ))
        }

        (Term::Fun(x, b), Elab::Fun(y, to, _)) => {
            // Make sure it's well typed before reducing it
            let mut xr = check(x, &Elab::Type, env)?;
            xr.whnf(env);
            // Because patterns are types, match checking amounts to subtype checking
            if y.subtype_of(&xr, &mut env.clone()) {
                // Add bindings in the argument to the environment with types given by `y`
                xr.match_types(y, env);
                // Update the types of binders in `xr` based on the type `y`
                xr.update_binders(y, env);

                let mut to = to.cloned(&mut env.clone());
                to.whnf(env);

                let be = check(b, &to, env)?;

                Ok(Elab::Fun(Box::new(xr), Box::new(be), Box::new(to)))
            } else {
                Err(TypeError::NotSubtypeF(
                    y.cloned(&mut env.clone()),
                    x.copy_span(xr),
                ))
            }
        }
        (_, Elab::Type) => {
            let t = synth(term, env)?;
            let ty = t.get_type(env);
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&Elab::Type, &mut env.clone()) {
                Ok(t)
            } else {
                Err(TypeError::NotType(
                    term.copy_span(ty.cloned(&mut env.clone())),
                ))
            }
        }
        (_, _) => {
            let t = synth(term, env)?;
            let ty = t.get_type(env);
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

impl Elab {
    fn update_binders<T: MainGroup>(&mut self, other: &Elab, env: &mut TempEnv<T>) {
        use Elab::*;
        match (&mut *self, other) {
            // We don't want `x:y:T`, and we already called match_types()
            (_, Binder(_, t)) => {
                self.update_binders(t, env);
            }
            (Binder(_, t), _) => {
                **t = other.cloned(&mut env.clone());
            }
            (Pair(ax, ay), Pair(bx, by)) => {
                ax.update_binders(bx, env);
                ay.update_binders(by, env);
            }
            (App(af, ax), App(bf, bx)) => {
                af.update_binders(bf, env);
                ax.update_binders(bx, env);
            }
            _ => (),
        }
    }

    /// Like do_match(), but fills in the types instead of Elabs
    fn match_types<T: MainGroup>(&self, other: &Elab, env: &mut TempEnv<T>) {
        use Elab::*;
        match (self, other) {
            // Since we match it against itself to apply binder types
            (Binder(na, _), Binder(nb, t)) if na == nb => {
                #[cfg(feature = "logging")]
                {
                    let b = &env.bindings();
                    println!(
                        "env: {} : {}",
                        self.pretty(b).ansi_string(),
                        t.pretty(b).ansi_string()
                    );
                }

                let t = t.cloned(&mut env.clone());
                env.set_ty(*na, t);
            }
            (Binder(s, t), _) => {
                #[cfg(feature = "logging")]
                {
                    let b = &env.bindings();
                    println!(
                        "type: {} : {}",
                        self.pretty(b).ansi_string(),
                        other.pretty(b).ansi_string()
                    );
                }

                // For alpha-equivalence - we need symbols in our body to match symbols in the other body if they're defined as the same
                other.do_match(&Var(*s, Box::new(t.cloned(&mut env.clone()))), env);

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
    pub fn subtype_of<T: MainGroup>(&self, sup: &Elab, env: &mut TempEnv<T>) -> bool {
        if !self.is_type() {
            return false;
        }
        match (self, sup) {
            (Elab::Struct(_, sub), Elab::Struct(_, sup)) => {
                // We DON'T do record subtyping, that's confusing and hard to compile efficiently
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
                    // Matching in either direction works, we have to check alpha equality
                    ax.match_types(bx, env);

                    // Since types are only in weak-head normal form, we have to reduce the spines to compare them
                    let mut ay = ay.cloned(env);
                    ay.whnf(env);
                    let mut by = by.cloned(env);
                    by.whnf(env);
                    ay.subtype_of(&by, env)
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
