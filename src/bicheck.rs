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
    WrongArity(usize, usize, Elab, Span),
    /// We tried to apply the given term, but it's not a function
    /// The `Elab` here is the type, the `Term` is the argument we tried to apply it to
    NotFunction(Spanned<Elab>, Spanned<Term>),
    /// The first Elab needs to be a subtype of the second one, but it's not
    NotSubtype(Spanned<Elab>, Elab),
    /// `NotSubtype` with flipped span information
    NotSubtypeF(Elab, Spanned<Elab>),
    /// `NotSubtype(_, TypeN)`
    WrongUniverse(Spanned<Elab>, u32, u32),
    /// No match branch matched
    NoBranch(Elab, Vec<Spanned<Elab>>),
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
            TypeError::NotFunction(f, x) => Error::new(
                file,
                Doc::start("Type error: not a function: '")
                    .chain(f.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                f.span(),
                Doc::start("this was applied to '")
                    .chain(x.pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::WrongArity(expected, found, ty, span) => Error::new(
                file,
                Doc::start("Type error: mismatched arity: expected function with ")
                    .add(expected)
                    .add(if expected == 1 {
                        " parameter"
                    } else {
                        " parameters"
                    })
                    .add(", found function with ")
                    .add(found)
                    .add(if found == 1 {
                        " parameter"
                    } else {
                        " parameters"
                    })
                    .style(Style::Bold),
                span,
                Doc::start("expected type '")
                    .chain(ty.unbind().pretty(b).style(Style::None))
                    .add("' with ")
                    .add(expected)
                    .add(if expected == 1 {
                        " parameter"
                    } else {
                        " parameters"
                    }),
            ),
            TypeError::WrongUniverse(sub, m, n) => Error::new(
                file,
                Doc::start("Type error: type '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("' is not in universe ")
                    .add(n)
                    .add(" and so is not a subtype of Type")
                    .add(n)
                    .style(Style::Bold),
                sub.span(),
                Doc::start("this has type '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("', which is in universe ")
                    .add(m),
            ),
            TypeError::NotSubtype(sub, sup) => Error::new(
                file,
                Doc::start("Type error: could not match types '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                sub.span(),
                Doc::start("this has type '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Note),
            ),
            TypeError::NotSubtypeF(sub, sup) => Error::new(
                file,
                Doc::start("Type error: could not match types '")
                    .chain(sub.unbind().pretty(b).style(Style::None))
                    .add("' and '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                sup.span(),
                Doc::start("this has type '")
                    .chain(sup.unbind().pretty(b).style(Style::None))
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
                    .chain(v.unbind().pretty(b).style(Style::None))
                    .add("'")
                    .style(Style::Bold),
                s.span(),
                format!("no such field"),
            ),
            TypeError::DuplicateField(x, y) => Error::new(
                file,
                Doc::start("Type error: multiple definitions of variable '")
                    .chain(x.pretty(b))
                    .add("' in struct or module")
                    .style(Style::Bold),
                x.span(),
                format!("first defined here"),
            )
            .with_label(file, y.span(), format!("redefined here")),
            TypeError::NoBranch(sub, sups) => {
                let mut e = Error::no_label(
                    Doc::start("Type error: no branch matched the type '")
                        .chain(sub.unbind().pretty(b).style(Style::None))
                        .add("'")
                        .style(Style::Bold),
                );
                for branch in sups {
                    e = e.with_label(
                        file,
                        branch.span(),
                        Doc::start("This branch has type '")
                            .chain(branch.unbind().pretty(b).style(Style::None))
                            .add("'")
                            .style(Style::Note)
                            .ansi_string(),
                    );
                }
                e
            }
        }
    }
}

/// Attempts to come up with a type for a term, returning the elaborated term
pub fn synth<T: MainGroup>(t: &STerm, env: &mut TempEnv<T>) -> Result<Elab, TypeError> {
    #[cfg(feature = "logging")]
    println!("synth ({})", t.pretty(&*env.bindings()).ansi_string());

    match &**t {
        Term::Type(i) => Ok(Elab::Type(*i)),
        Term::Builtin(b) => Ok(Elab::Builtin(*b)),
        Term::Var(x) => {
            let ty = env
                .ty(*x)
                .map(|x| x.cloned(&mut Cloner::new(&env)))
                .ok_or_else(|| TypeError::NotFound(t.copy_span(*x)))?
                .whnf(env);
            Ok(Elab::Var(*x, Box::new(ty)))
        }
        Term::I32(i) => Ok(Elab::I32(*i)),
        Term::Unit => Ok(Elab::Unit),
        Term::Tag(t) => Ok(Elab::Tag(*t)),
        Term::Pair(x, y) => {
            // TODO I don't think this covers dependent pairs
            let x = synth(x, env)?;
            let y = synth(y, env)?;
            Ok(Elab::Pair(Box::new(x), Box::new(y)))
        }
        Term::Struct(id, iv) => {
            if env.tys.keys().any(|k| t.uses(*k)) {
                // If it captures local variables, we compile in "struct mode"
                // TODO a note in "not found" error messages here that structs that capture variables are ordered
                let mut rv = Vec::new();
                for (k, v) in iv {
                    let v = synth(v, env)?;
                    let t = v.get_type(env);
                    env.set_ty(**k, t);
                    rv.push((**k, v));
                }

                Ok(Elab::StructInline(rv))
            } else {
                // Otherwise, compile in Salsa-enabled "module mode"
                let scope = ScopeId::Struct(*id, Box::new(env.scope()));
                env.db.add_mod(*id, env.scope.file(), iv);

                // Record any type errors inside the module
                for sym in env.db.symbols(scope.clone()).iter() {
                    env.db.elab(scope.clone(), **sym);
                }

                Ok(Elab::StructIntern(*id))
            }
        }
        Term::App(fi, x) => {
            let f = synth(fi, env)?;
            let x = match f.get_type(env) {
                Elab::Fun(cl, v) => {
                    env.add_clos(&cl);
                    // We check the argument against a union of first parameter types across all branches
                    let from: Vec<_> = v.into_iter().map(|(mut x, _, _)| x.remove(0)).collect();
                    let from = Elab::Union(from).whnf(env).simplify_unions(env);
                    check(x, &from, env)?
                }
                Elab::Tag(_) | Elab::App(_, _) | Elab::Bottom => synth(x, env)?,
                a => {
                    return Err(TypeError::NotFunction(
                        fi.copy_span(a.cloned(&mut Cloner::new(&env))),
                        x.clone(),
                    ))
                }
            };
            Ok(Elab::App(Box::new(f), Box::new(x)))
        }
        Term::Project(r, m) => {
            let r = synth(r, env)?;
            let rt = r.get_type(env);
            match &r.get_type(env) {
                Elab::StructInline(v) => {
                    if let Some((_, val)) = v.iter().find(|(name, _)| name.raw() == **m) {
                        val.cloned(&mut Cloner::new(&env))
                    } else {
                        return Err(TypeError::NoSuchField(
                            m.clone(),
                            rt.cloned(&mut Cloner::new(&env)),
                        ));
                    }
                }
                _ => {
                    return Err(TypeError::NoSuchField(
                        m.clone(),
                        rt.cloned(&mut Cloner::new(&env)),
                    ))
                }
            };
            Ok(Elab::Project(Box::new(r), **m))
        }
        Term::Fun(iv) => {
            let mut rv = Vec::new();
            for (xs, y) in iv {
                let mut rx = Vec::new();
                for x in xs {
                    // Make sure it's well typed before reducing it
                    let x = synth(x, env)?.whnf(env);
                    // Match it with itself to apply the types
                    x.match_types(&x, env);

                    rx.push(x);
                }

                let y = synth(y, env)?;
                // get_type() should always produce WHNF, so we don't need whnf() here
                let to = y.get_type(env);

                rv.push((rx, y, to))
            }
            Ok(Elab::Fun(env.clos(t), rv))
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
                        let val = synth(val, env)?;
                        let ty = val.get_type(env);
                        env.set_ty(**name, ty);
                        // Blocks can be dependent!
                        let val = val.whnf(env);
                        env.set_val(**name, val.cloned(&mut Cloner::new(&env)));
                        rv.push(ElabStmt::Def(**name, val));
                    }
                }
            }
            Ok(Elab::Block(rv))
        }
        Term::The(ty, u) => {
            // Make sure it's well typed before reducing it
            let ty = synth(ty, env)?.whnf(env);
            let ue = check(u, &ty, env)?;
            Ok(ue)
        }
        Term::Binder(x, Some(ty)) => {
            let ty = synth(ty, env)?.whnf(env);
            Ok(Elab::Binder(*x, Box::new(ty)))
        }
        Term::Binder(x, None) => Ok(Elab::Binder(*x, Box::new(Elab::Top))),
        Term::Union(iv) => {
            let mut rv = Vec::new();
            for val in iv {
                let val = synth(val, env)?;
                rv.push(val);
            }
            Ok(Elab::Union(rv).simplify_unions(env))
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
            let mut cln = Cloner::new(env);
            let (tx, ty) = (tx.cloned(&mut cln).whnf(env), ty.cloned(&mut cln).whnf(env));
            // TODO dependent pairs don't really work
            check(x, &tx, env)?;
            check(y, &ty, env)
        }

        // As far as we know, it could be any type
        (Term::Binder(s, None), _) /*if typ.subtype_of(&Elab::Type, &mut env.clone())*/ => {
            // As far as we know, it could be anything, so it's `Top`
            // We'll narrow it down with `update_binders()` later, if we can
            Ok(Elab::Binder(*s, Box::new(Elab::Top)))
        }

        (Term::Fun(v), Elab::Fun(cl, v2)) => {
            env.add_clos(cl);
            let mut cln = Cloner::new(env);
            let mut v2: Vec<_> = v2
                .iter()
                .map(|(x, y, z)| {
                    (
                        x.iter().map(|x| x.cloned(&mut cln)).collect::<Vec<_>>(),
                        y.cloned(&mut cln),
                        z.cloned(&mut cln),
                    )
                })
                .collect();
            let mut v = v.clone();

            // To propagate a type error out of several nested closures
            let mut error: Option<TypeError> = None;
            // If the value has more parameters than the type, we curry the result type into the function type
            while v[0].0.len() > v2[0].0.len() {
                v2 = v2
                    .into_iter()
                    .flat_map(|(mut arg, body, _)| {
                        let body = body.whnf(env);
                        match body {
                            Elab::Fun(cl, v3) => {
                                env.add_clos(&cl);
                                v3
                                    .into_iter()
                                    .map(|(mut from, to, _)| {
                                        arg.append(&mut from);
                                        (
                                            arg.iter().map(|x| x.cloned(&mut cln)).collect(),
                                            to.cloned(&mut cln),
                                            to.get_type(env),
                                        )
                                    })
                                    .collect::<Vec<_>>()
                            }
                            _ => {
                                error = Some(TypeError::WrongArity(
                                    arg.len(),
                                    v[0].0.len(),
                                    typ.cloned(&mut cln),
                                    term.span(),
                                ));
                                Vec::new()
                            }
                        }
                    })
                    .collect();
                if error.is_some() {
                    break;
                }
            }
            if let Some(e) = error {
                return Err(e);
            }

            // If the type has more parameters than the value
            // So we add an extra parameter and apply it to the body
            // `f : fun Int => Int = id Int` --> `f : fun Int => Int = fun x: => id Int x`
            // We store the arity before this transformation for error messages
            let initial_arity = v[0].0.len();
            while v[0].0.len() < v2[0].0.len() {
                for (arg, body) in &mut v {
                    let extra_param = env.bindings_mut().create("$curry".to_string());
                    arg.push(
                        arg.last()
                            .unwrap()
                            .copy_span(Term::Binder(extra_param, None)),
                    );
                    *body = body.copy_span(Term::App(
                        body.clone(),
                        arg.last().unwrap().copy_span(Term::Var(extra_param)),
                    ));
                }
            }
            debug_assert_eq!(v[0].0.len(), v2[0].0.len());

            // If the type has parameters with union types, flatten them into function branches so we can match more easily
            let v2: Vec<(Vec<Elab>, Elab)> = v2
                .into_iter()
                .flat_map(|(from, to, _)| {
                    from.into_iter()
                        .map(|from| match from {
                            Elab::Union(v) => v,
                            from => vec![from],
                        })
                        .fold(vec![Vec::new()], |cases: Vec<Vec<Elab>>, arg_cases| {
                            cases
                                .into_iter()
                                .flat_map(|x| {
                                    arg_cases
                                        .iter()
                                        .map(|y| {
                                            let mut x: Vec<_> =
                                                x.iter().map(|x| x.cloned(&mut cln)).collect();
                                            x.push(y.cloned(&mut cln));
                                            x
                                        })
                                        .collect::<Vec<_>>()
                                })
                                .collect()
                        })
                        .into_iter()
                        .map(|x| (x, to.cloned(&mut cln)))
                        .collect::<Vec<_>>()
                })
                .collect();

            // Start by typechecking all parameters of all branches and marking them as not used yet
            let mut unused = Vec::new();
            for (args, body) in v {
                let mut ra = Vec::new();
                for a in args {
                    let e = synth(&a, env)?.whnf(env);
                    ra.push((e, a.span()));
                }
                unused.push((ra, body));
            }

            // Only put the branches we need based on the type in `used`
            let mut used: Vec<(Vec<(Elab, Span)>, Elab, Elab)> = Vec::new();
            for (from, to) in v2 {
                let mut errors: Vec<Vec<Spanned<Elab>>> =
                    (0..from.len()).map(|_| Vec::new()).collect();

                // Try the branches we already used first - they're higher priority
                let mut passed = false;
                for (args, _, _) in used.iter() {
                    let mut all_subtype = true;
                    // Go through the curried parameters and make sure each one matches
                    for ((i, f), (a, span)) in from.iter().enumerate().zip(args) {
                        if !f.subtype_of(&a, env) {
                            errors[i].push(Spanned::new(a.cloned(&mut cln), *span));
                            all_subtype = false;
                            break;
                        }
                    }
                    if all_subtype {
                        passed = true;
                        break;
                    }
                }
                if passed {
                    continue;
                }

                // Now try the unused branches
                // We'll put any ones that didn't here and replace unused with it at the end
                let mut unused_next = Vec::new();
                let mut passed = false;
                for (args, body) in unused {
                    if passed {
                        unused_next.push((args, body));
                        continue;
                    }
                    let mut all_subtype = true;
                    let mut ra = Vec::new();
                    // Go through the curried parameters and make sure each one matches
                    for ((i, f), (mut a, span)) in from.iter().enumerate().zip(args) {
                        if !all_subtype {
                        } else if !f.subtype_of(&a, env) {
                            errors[i].push(Spanned::new(a.cloned(&mut cln), span));
                            all_subtype = false;
                        } else {
                            // Update the types of binders in `xr` based on the type `y`
                            a.update_binders(f, env);
                            // Add bindings in the argument to the environment with types given by `y`
                            a.match_types(f, env);
                            a = a.whnf(env);
                        }
                        ra.push((a, span));
                    }
                    if all_subtype {
                        passed = true;
                        // If all the parameters matched, this branch of the type is covered, so no errors yet
                        errors = Vec::new();

                        let to = to.cloned(&mut cln).whnf(env);
                        let body = match check(&body, &to, env) {
                            Ok(x) => x,
                            Err(TypeError::NotFunction(f, x)) => match &*x {
                                // We added a parameter for currying, but it didn't work
                                Term::Var(s) if env.bindings().resolve(*s) == "$curry" => return Err(TypeError::WrongArity(
                                    from.len(),
                                    initial_arity,
                                    typ.cloned(&mut cln),
                                    term.span(),
                                )),
                                _ => return Err(TypeError::NotFunction(f, x)),
                            }
                            Err(e) => return Err(e),
                        };

                        used.push((ra, body, to));
                    } else {
                        unused_next.push((ra, body));
                    }
                }
                unused = unused_next;

                for (i, v) in errors.into_iter().enumerate() {
                    if !v.is_empty() {
                        return Err(TypeError::NoBranch(from[i].cloned(&mut cln), v));
                    }
                }
            }
            // TODO give a warning if there's anything left in `unused`

            Ok(Elab::Fun(
                env.clos(term),
                used.into_iter()
                    .map(|(a, b, c)| (a.into_iter().map(|(x, _)| x).collect(), b, c))
                    .collect(),
            ))
        }
        (Term::App(f, x), Elab::App(tf, tx)) => {
            let f = check(f, tf, env)?;
            let x = check(x, tx, env)?;
            Ok(Elab::App(Box::new(f), Box::new(x)))
        }
        (Term::App(f, x), Elab::Type(i)) if f.tag_head(env) => {
            let f = check(f, &Elab::Type(*i), env)?;
            let x = check(x, &Elab::Type(*i), env)?;
            Ok(Elab::App(Box::new(f), Box::new(x)))
        }
        (_, _) => {
            let t = synth(term, env)?;
            let ty = t.get_type(env);
            // Is it guaranteed to be a `typ`?
            if ty.subtype_of(&typ, &mut env.clone()) {
                Ok(t)
            } else {
                match typ.unbind() {
                    Elab::Type(i) => Err(TypeError::WrongUniverse(
                        term.copy_span(ty.cloned(&mut Cloner::new(&env))),
                        ty.universe(env) - 1,
                        *i,
                    )),
                    _ => Err(TypeError::NotSubtype(
                        term.copy_span(ty.cloned(&mut Cloner::new(&env))),
                        typ.cloned(&mut Cloner::new(&env)),
                    )),
                }
            }
        }
    }
}

impl Term {
    fn tag_head<T: MainGroup>(&self, env: &TempEnv<T>) -> bool {
        match self {
            Term::Tag(_) => true,
            Term::App(f, _) => f.tag_head(env),
            Term::Var(x) => env
                .db
                .elab(env.scope.clone(), *x)
                .map(|x| x.get_type(&mut env.clone()))
                .or_else(|| env.ty(*x).map(|x| x.cloned(&mut Cloner::new(&env))))
                .map_or(false, |x| x.tag_head()),
            _ => false,
        }
    }
}

impl Elab {
    fn tag_head(&self) -> bool {
        match self {
            Elab::Tag(_) => true,
            Elab::App(f, _) => f.tag_head(),
            Elab::Var(_, t) => t.tag_head(),
            _ => false,
        }
    }

    fn update_binders<T: MainGroup>(&mut self, other: &Elab, env: &TempEnv<T>) {
        use Elab::*;
        match (&mut *self, other) {
            // We don't want `x:y:T`, and we already called match_types()
            (_, Binder(_, t)) => {
                self.update_binders(t, env);
            }
            (Binder(_, t), _) => {
                **t = other.cloned(&mut Cloner::new(&env));
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
    pub fn match_types<T: MainGroup>(&self, other: &Elab, env: &mut TempEnv<T>) {
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

                let t = t.cloned(&mut Cloner::new(&env));
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
                other.do_match(&Var(*s, Box::new(t.cloned(&mut Cloner::new(&env)))), env);

                let other = other.cloned(&mut Cloner::new(&env));
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
            (App(af, ax), App(bf, bx)) => {
                af.match_types(bf, env);
                ax.match_types(bx, env);
            }
            _ => (),
        }
    }

    /// <=; every `self` is also a `sup`
    /// Not that this is *the* way to check type equality
    pub fn subtype_of<T: MainGroup>(&self, sup: &Elab, env: &mut TempEnv<T>) -> bool {
        match (self, sup) {
            (Elab::Bottom, _) => true,
            (_, Elab::Top) => true,
            (Elab::I32(n), Elab::I32(m)) => n == m,
            (Elab::I32(_), Elab::Builtin(Builtin::Int)) => true,
            (Elab::StructInline(sub), Elab::StructInline(sup)) => {
                // We DON'T do record subtyping, that's confusing and hard to compile efficiently
                sup.iter().all(|(n, sup)| sub.iter().find(|(n2, _)| n2.raw() == n.raw()).map_or(false, |(_, sub)| sub.subtype_of(sup, env)))
                    // so make sure there aren't any extra fields
                    && sub.iter().all(|(n, _)| sup.iter().any(|(n2, _)| n2.raw() == n.raw()))
            }
            (Elab::Tag(x), Elab::Tag(y)) if x == y => true,
            (Elab::Builtin(b), Elab::Builtin(c)) if b == c => true,
            (Elab::Unit, Elab::Unit) => true,
            (Elab::Var(x, _), _) if env.db.elab(env.scope(), *x).is_some() => env
                .db
                .elab(env.scope(), *x)
                .unwrap()
                .cloned(&mut Cloner::new(env))
                .subtype_of(sup, env),
            (_, Elab::Var(x, _)) if env.db.elab(env.scope(), *x).is_some() => self.subtype_of(
                &env.db
                    .elab(env.scope(), *x)
                    .unwrap()
                    .cloned(&mut Cloner::new(env)),
                env,
            ),
            (Elab::Var(x, _), _) if env.vals.contains_key(x) => env
                .val(*x)
                .unwrap()
                .cloned(&mut Cloner::new(env))
                .subtype_of(sup, env),
            (_, Elab::Var(x, _)) if env.vals.contains_key(x) => {
                self.subtype_of(&env.val(*x).unwrap().cloned(&mut Cloner::new(env)), env)
            }
            (Elab::App(f1, x1), Elab::App(f2, x2)) => {
                f1.subtype_of(f2, env) && x1.subtype_of(x2, env)
            }
            (Elab::Pair(ax, ay), Elab::Pair(bx, by)) => {
                ax.subtype_of(bx, env) && ay.subtype_of(by, env)
            }
            // (Type -> (Type, Type)) <= ((Type, Type) -> Type)
            (Elab::Fun(cl_a, v_sub), Elab::Fun(cl_b, v_sup)) => {
                env.add_clos(cl_a);
                env.add_clos(cl_b);
                for (args_sup, to_sup, _) in v_sup.iter() {
                    let mut found = false;
                    for (args_sub, to_sub, _) in v_sub.iter() {
                        let mut all_subtype = true;
                        for (sup, sub) in args_sup.iter().zip(args_sub.iter()) {
                            // Function parameters are contravariant
                            if !sup.subtype_of(sub, env) {
                                all_subtype = false;
                                break;
                            }
                            // Matching in either direction works, we have to check alpha equality
                            sub.match_types(sup, env);
                        }

                        if !all_subtype {
                            break;
                        }

                        // Since types are only in weak-head normal form, we have to reduce the spines to compare them
                        let to_sup = to_sup.cloned(&mut Cloner::new(env)).whnf(env);
                        let to_sub = to_sub.cloned(&mut Cloner::new(env)).whnf(env);

                        if to_sub.subtype_of(&to_sup, env) {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return false;
                    }
                }
                return true;
            }
            // Two variables that haven't been resolved yet, but refer to the same definition
            (Elab::Var(x, _), Elab::Var(y, _)) if y == x => true,
            (Elab::Binder(_, t), _) => t.subtype_of(sup, env),
            (_, Elab::Binder(_, t)) => self.subtype_of(t, env),
            (Elab::Union(sub), Elab::Union(sup)) => {
                // If each type in `sub` has a supertype in `sup`, we're good
                let mut sub: Vec<_> = sub.iter().collect();
                for sup in sup.iter() {
                    let mut i = 0;
                    while i < sub.len() {
                        let x = sub[i];

                        if x.subtype_of(&sup, env) {
                            sub.remove(i);
                        } else {
                            i += 1;
                        }
                    }
                }
                sub.is_empty()
            }
            (Elab::Union(v), _) => v.iter().all(|x| x.subtype_of(sup, env)),
            (_, Elab::Union(v)) => v.iter().any(|x| self.subtype_of(x, env)),
            // Higher universes contain lower ones
            (Elab::Type(a), Elab::Type(b)) => b >= a,
            // Due to singleton types, pretty much everything (except unions) can be its own type, so everything can be a type of types
            // So if it's in universe `N+1` or below, all it's values are in universe `N`, so it's a subtype of `TypeN`
            (_, Elab::Type(i)) => self.universe(env) <= i + 1,
            _ => false,
        }
    }
}
