use crate::common::*;
use crate::elaborate::*;
use crate::term::*;
use bit_set::BitSet;
use durin::ir::Width;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pat {
    Any,
    Var(Name, Box<VTy>),
    Cons(DefId, Box<VTy>, Vec<Pat>),
    Or(Box<Pat>, Box<Pat>),
    Lit(Literal, Width),
    Bool(bool),
    /// eff p k :: E
    Eff(Box<Val>, Box<Pat>, Box<Pat>),
    EffRet(Box<Pat>),
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Cov {
    /// We covered everything, there's nothing left
    All,
    /// We didn't cover anything yet
    None,
    /// We *did* cover these constructors
    Cons(Vec<(DefId, Vec<Cov>)>),
    /// We *did* cover these literals
    Lit(BitSet),
    /// we *did* cover this Bool
    Bool(bool),
    Eff(Box<Cov>, Vec<(Val, Cov)>),
}
impl Take for Cov {
    fn take(&mut self) -> Self {
        let mut new = Cov::None;
        std::mem::swap(self, &mut new);
        new
    }
}
impl Cov {
    pub fn or(self, other: Self, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match (self, other) {
            (Cov::All, _) | (_, Cov::All) => Cov::All,
            (Cov::None, x) | (x, Cov::None) => x,
            (Cov::Bool(x), Cov::Bool(y)) if x != y => Cov::All,
            (Cov::Bool(x), Cov::Bool(_)) => Cov::Bool(x),
            (Cov::Lit(mut a), Cov::Lit(b)) => {
                a.union_with(&b);
                Cov::Lit(a)
            }
            (Cov::Cons(mut v), Cov::Cons(v2)) => {
                for (cons, cov) in v2 {
                    if let Some((_, cov2)) = v.iter_mut().find(|(c, _)| *c == cons) {
                        *cov2 = std::mem::take(cov2)
                            .into_iter()
                            .zip(cov)
                            .map(|(x, y)| x.or(y, mcxt, db))
                            .collect();
                    } else {
                        v.push((cons, cov));
                    }
                }
                Cov::Cons(v)
            }
            (Cov::Eff(mut a, mut v), Cov::Eff(a2, v2)) => {
                for (eff, cov) in v2 {
                    if let Some((_, cov2)) = v.iter_mut().find(|(e, _)| {
                        unify(
                            e.clone(),
                            eff.clone(),
                            mcxt.size,
                            Span::empty(),
                            db,
                            &mut mcxt.clone(),
                        )
                        .unwrap_or(false)
                    }) {
                        *cov2 = cov2.take().or(cov, mcxt, db);
                    } else {
                        v.push((eff, cov));
                    }
                }
                *a = a.or(*a2, mcxt, db);
                Cov::Eff(a, v)
            }
            _ => unreachable!(),
        }
    }

    pub fn pretty_rest(&self, ty: &VTy, db: &dyn Compiler, mcxt: &MCxt) -> Doc {
        match self {
            Cov::All => Doc::start("<nothing>"),
            Cov::None if matches!(ty, Val::App(Var::Builtin(Builtin::UnitType), _, _, _)) => {
                Doc::start("()")
            }
            Cov::None => Doc::start("_"),
            // We don't show what literals we've covered.
            // In the future, we may switch to ranges like Rust uses.
            Cov::Lit(_) => Doc::start("_"),
            Cov::Bool(b) => Doc::start(match b {
                // What's *uncovered*?
                false => "True",
                true => "False",
            }),
            Cov::Cons(covs) => {
                let mut mcxt = mcxt.clone();
                mcxt.define(db.intern_name("_".into()), NameInfo::Local(Val::Type), db);

                let ty = ty.clone().inline(mcxt.size, db, &mcxt);
                let sid = match &ty {
                    Val::App(Var::Type(_, sid), _, _, _) => *sid,
                    _ => panic!(
                        "Called Cov::pretty_rest() on a Cov::Cons but passed non-datatype {:?}",
                        ty
                    ),
                };

                let mut v = Vec::new();
                let mut unmatched: Vec<DefId> = db
                    .lookup_intern_scope(sid)
                    .iter()
                    .filter_map(|&(_name, id)| {
                        let info = db.elaborate_def(id).ok()?;
                        match &*info.term {
                            Term::Var(Var::Cons(cid), _) if id == *cid => {
                                let cty = IntoOwned::<Val>::into_owned(info.typ)
                                    .cons_ret_type(mcxt.size, &mcxt, db);
                                if crate::elaborate::local_unify(
                                    cty,
                                    ty.clone(),
                                    mcxt.size,
                                    Span::empty(),
                                    db,
                                    &mut mcxt.clone(),
                                )
                                .ok()?
                                {
                                    Some(id)
                                } else {
                                    println!(
                                        "Skipping constructor {}",
                                        info.term
                                            .pretty(db, &mut Names::new(mcxt.cxt, db))
                                            .ansi_string()
                                    );
                                    None
                                }
                            }
                            _ => None,
                        }
                    })
                    .collect();

                for (cons, args) in covs {
                    unmatched.retain(|id| id != cons);
                    if args.iter().any(|x| *x != Cov::All) {
                        let (pre, _) = db.lookup_intern_def(*cons);
                        let pre = db.lookup_intern_predef(pre);
                        let name = pre.name().unwrap();

                        let mut cons_ty = (*db
                            .elaborate_def(*cons)
                            .expect("probably an invalid constructor?")
                            .typ)
                            .clone();
                        let mut l = mcxt.size;

                        let mut v2 = vec![Doc::start(name.get(db))];
                        for x in args {
                            let ty = match cons_ty {
                                // TODO effect constructors
                                Val::Fun(from, to, _) => {
                                    cons_ty = *to;
                                    *from
                                }
                                Val::Pi(_, cl, _) => {
                                    let from = cl.ty.clone();
                                    cons_ty = cl.vquote(l.inc(), &mcxt, db);
                                    l = l.inc();
                                    from
                                }
                                _ => unreachable!(),
                            };
                            v2.push(x.pretty_rest(&ty, db, &mcxt));
                        }

                        v.push(Doc::intersperse(v2, Doc::none().space()));
                    }
                }

                for cons in unmatched {
                    let (pre, _) = db.lookup_intern_def(cons);
                    let pre = db.lookup_intern_predef(pre);
                    let name = pre.name().unwrap();

                    let mut cons_ty = (*db
                        .elaborate_def(cons)
                        .expect("probably an invalid constructor?")
                        .typ)
                        .clone();
                    let mut l = mcxt.size;

                    let mut v2 = vec![Doc::start(name.get(db))];
                    loop {
                        let from = match cons_ty {
                            // TODO effect constructors
                            Val::Fun(from, to, _) => {
                                cons_ty = *to;
                                *from
                            }
                            Val::Pi(_, to, _) => {
                                let from = to.ty.clone();
                                cons_ty = to.vquote(l.inc(), &mcxt, db);
                                l = l.inc();
                                from
                            }
                            _ => break,
                        };
                        v2.push(Cov::None.pretty_rest(&from, db, &mcxt));
                    }

                    v.push(Doc::intersperse(v2, Doc::none().space()));
                }

                Doc::intersperse(v, Doc::start(" | "))
            }
            Cov::Eff(a, v) => {
                let mut d = None;
                if !matches!(&**a, Cov::All) {
                    d = Some(a.pretty_rest(ty, db, mcxt));
                }
                for (e, c) in v {
                    if !matches!(c, Cov::All) {
                        d = Some(match d {
                            Some(d) => d.add(" | ").chain(
                                Doc::keyword("eff")
                                    .space()
                                    .chain(c.pretty_rest(&e, db, mcxt).nest(Prec::Atom))
                                    .add(" _"),
                            ),
                            None => Doc::keyword("eff")
                                .space()
                                .chain(c.pretty_rest(e, db, mcxt).nest(Prec::Atom))
                                .add(" _"),
                        });
                    }
                }
                d.expect("Empty Cov::Eff")
            }
        }
    }

    pub fn simplify(self, ty: &VTy, db: &dyn Compiler, mcxt: &MCxt) -> Self {
        match self {
            Cov::All => Cov::All,
            Cov::None => Cov::None,
            Cov::Lit(s) => Cov::Lit(s),
            Cov::Bool(x) => Cov::Bool(x),
            Cov::Cons(mut covs) => {
                let mut mcxt = mcxt.clone();
                mcxt.define(db.intern_name("_".into()), NameInfo::Local(Val::Type), db);

                let ty = ty.clone().inline(mcxt.size, db, &mcxt);
                let sid = match &ty {
                    Val::App(Var::Type(_, sid), _, _, _) => *sid,
                    _ => panic!(
                        "Called Cov::simplify() on a Cov::Cons but passed non-datatype {:?}",
                        ty
                    ),
                };
                let mut unmatched: Vec<DefId> = db
                    .lookup_intern_scope(sid)
                    .iter()
                    .filter_map(|&(_name, id)| {
                        let info = db.elaborate_def(id).ok()?;
                        match &*info.term {
                            Term::Var(Var::Cons(cid), _) if id == *cid => {
                                let cty = IntoOwned::<Val>::into_owned(info.typ)
                                    .cons_ret_type(mcxt.size, &mcxt, db);
                                if crate::elaborate::local_unify(
                                    cty,
                                    ty.clone(),
                                    mcxt.size,
                                    Span::empty(),
                                    db,
                                    &mut mcxt.clone(),
                                )
                                .ok()?
                                {
                                    Some(id)
                                } else {
                                    println!(
                                        "Skipping constructor {}",
                                        info.term
                                            .pretty(db, &mut Names::new(mcxt.cxt, db))
                                            .ansi_string()
                                    );
                                    None
                                }
                            }
                            _ => None,
                        }
                    })
                    .collect();
                for (cons, args) in &mut covs {
                    let mut cons_ty = (*db
                        .elaborate_def(*cons)
                        .expect("probably an invalid constructor?")
                        .typ)
                        .clone()
                        .inline_metas(&mcxt, db);
                    let mut l = mcxt.size;

                    for x in std::mem::take(args) {
                        let ty = match cons_ty {
                            // TODO effect constructors
                            Val::Fun(from, to, _) => {
                                cons_ty = *to;
                                *from
                            }
                            Val::Pi(_, cl, _) => {
                                let from = cl.ty.clone();
                                cons_ty = cl.vquote(l.inc(), &mcxt, db);
                                l = l.inc();
                                from
                            }
                            _ => unreachable!(),
                        };
                        args.push(x.simplify(&ty, db, &mcxt));
                    }

                    if args.iter().all(|x| *x == Cov::All) {
                        // This pattern is guaranteed to cover this constructor completely
                        unmatched.retain(|id| id != cons);
                    }
                }

                if unmatched.is_empty() {
                    Cov::All
                } else {
                    Cov::Cons(covs)
                }
            }
            Cov::Eff(mut a, mut v) => {
                *a = a.simplify(ty, db, mcxt);
                let mut all_all = true;
                for (e, c) in &mut v {
                    *c = c.take().simplify(&e, db, mcxt);
                    all_all &= matches!(c, Cov::All);
                }
                if !all_all || !matches!(&*a, Cov::All) {
                    Cov::Eff(a, v)
                } else {
                    Cov::All
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum MatchResult {
    Yes(Env),
    No,
    Maybe,
}

impl Pat {
    pub fn cov(&self, mcxt: &MCxt, db: &dyn Compiler) -> Cov {
        match self {
            Pat::Any => Cov::All,
            Pat::Var(_, _) => Cov::All,
            Pat::Cons(id, _, v) => {
                Cov::Cons(vec![(*id, v.iter().map(|x| x.cov(mcxt, db)).collect())])
            }
            Pat::Or(x, y) => x.cov(mcxt, db).or(y.cov(mcxt, db), mcxt, db),
            Pat::Lit(l, _) => Cov::Lit(std::iter::once(l.to_usize()).collect()),
            Pat::Bool(b) => Cov::Bool(*b),
            Pat::Eff(e, p, k) => {
                assert_eq!(k.cov(mcxt, db), Cov::All);
                // TODO Cov can have a lifetime tied to its Pat and borrow the Val
                Cov::Eff(Box::new(Cov::None), vec![((**e).clone(), p.cov(mcxt, db))])
            }
            Pat::EffRet(p) => Cov::Eff(Box::new(p.cov(mcxt, db)), Vec::new()),
        }
    }

    pub fn pretty(&self, db: &dyn Compiler, names: &mut Names) -> Doc {
        match self {
            Pat::Any => Doc::start("_"),
            Pat::Var(n, _ty) => {
                let n = names.disamb(*n, db);
                names.add(n);
                Doc::start(n.get(db))
            }
            Pat::Cons(id, _, p) => Doc::start(
                db.lookup_intern_predef(db.lookup_intern_def(*id).0)
                    .name()
                    .unwrap()
                    .get(db),
            )
            .chain(Doc::intersperse(
                p.iter().map(|x| {
                    Doc::none()
                        .space()
                        .chain(x.pretty(db, names).nest(Prec::Atom))
                }),
                Doc::none(),
            ))
            .prec(Prec::App),
            Pat::Or(x, y) => x
                .pretty(db, names)
                .space()
                .add('|')
                .space()
                .chain(y.pretty(db, names)),
            Pat::Lit(x, _) => x.pretty(),
            Pat::Bool(b) => Doc::start(match b {
                true => "True",
                false => "False",
            }),
            Pat::Eff(_, p, k) => {
                names.add(names.hole_name());
                Doc::keyword("eff")
                    .space()
                    .chain(p.pretty(db, names).nest(Prec::Atom))
                    .space()
                    .chain(k.pretty(db, names).nest(Prec::Atom))
                    .prec(Prec::App)
            }
            Pat::EffRet(x) => x.pretty(db, names),
        }
    }

    pub fn add_locals(&self, mcxt: &mut MCxt, db: &dyn Compiler) {
        match self {
            Pat::Any | Pat::Lit(_, _) | Pat::Bool(_) => {}
            Pat::Var(n, ty) => mcxt.define(*n, NameInfo::Local((**ty).clone()), db),
            Pat::Cons(_, _, v) => {
                for p in v {
                    p.add_locals(mcxt, db);
                }
            }
            Pat::Or(_, _) => {
                // Right now we don't allow bindings in or-patterns
            }
            Pat::Eff(_, p, k) => {
                // A hidden local for the effect return type
                mcxt.define(db.intern_name("_".into()), NameInfo::Local(Val::Type), db);
                p.add_locals(mcxt, db);
                k.add_locals(mcxt, db);
            }
            Pat::EffRet(p) => p.add_locals(mcxt, db),
        }
    }

    pub fn add_names(&self, l: Lvl, names: &mut Names) -> Lvl {
        match self {
            Pat::Any | Pat::Lit(_, _) | Pat::Bool(_) => l,
            Pat::Var(n, _) => {
                names.add(*n);
                l.inc()
            }
            Pat::Cons(_, _, v) => v.iter().fold(l, |l, p| p.add_names(l, names)),
            Pat::Or(_, _) => l,
            Pat::Eff(_, p, k) => {
                // A hidden local for the effect return type
                names.add(names.hole_name());
                let l = p.add_names(l.inc(), names);
                k.add_names(l, names)
            }
            Pat::EffRet(p) => p.add_names(l, names),
        }
    }

    pub fn eval_quote(self, env: &mut Env, l: &mut Lvl, mcxt: &MCxt, db: &dyn Compiler) -> Self {
        match self {
            Pat::Any => Pat::Any,
            Pat::Var(n, mut t) => {
                *t = t.inline_metas(mcxt, db);
                env.push(None);
                *l = l.inc();
                Pat::Var(n, t)
            }
            Pat::Cons(x, mut ty, y) => {
                *ty = ty.inline_metas(mcxt, db);
                Pat::Cons(
                    x,
                    ty,
                    y.into_iter()
                        .map(|x| x.eval_quote(env, l, mcxt, db))
                        .collect(),
                )
            }
            Pat::Or(mut x, mut y) => {
                *x = x.eval_quote(env, l, mcxt, db);
                *y = y.eval_quote(env, l, mcxt, db);
                Pat::Or(x, y)
            }
            Pat::Lit(x, w) => Pat::Lit(x, w),
            Pat::Bool(x) => Pat::Bool(x),
            Pat::Eff(mut e, mut p, mut k) => {
                env.push(None);
                *l = l.inc();
                *e = e.inline_metas(mcxt, db);
                *p = p.eval_quote(env, l, mcxt, db);
                *k = k.eval_quote(env, l, mcxt, db);
                Pat::Eff(e, p, k)
            }
            Pat::EffRet(mut x) => {
                *x = x.eval_quote(env, l, mcxt, db);
                Pat::EffRet(x)
            }
        }
    }

    pub fn match_with(
        &self,
        val: &Val,
        mut env: Env,
        mcxt: &MCxt,
        db: &dyn Compiler,
    ) -> MatchResult {
        use MatchResult::*;
        match self {
            Pat::Any => Yes(env),
            Pat::Var(_, _) => {
                env.push(Some(val.clone()));
                Yes(env)
            }
            Pat::Cons(id, _, v) => match val.clone().inline(env.size, db, mcxt) {
                Val::App(Var::Cons(id2), _, sp, _) => {
                    if *id == id2 {
                        let mut any_maybe = false;
                        for (i, (_, val)) in v.iter().zip(&sp) {
                            match i.match_with(val, env.clone(), mcxt, db) {
                                Yes(e2) => env = e2,
                                No => return No,
                                Maybe => any_maybe = true,
                            }
                        }
                        if any_maybe {
                            Maybe
                        } else {
                            Yes(env)
                        }
                    } else {
                        No
                    }
                }
                _ => Maybe,
            },
            Pat::Lit(x, _) => match val.unarc() {
                Val::Lit(l, _) => {
                    if l == x {
                        Yes(env)
                    } else {
                        No
                    }
                }
                _ => Maybe,
            },
            Pat::Bool(x) => match val.unarc() {
                Val::App(Var::Builtin(Builtin::True), _, _, _) => {
                    if *x {
                        Yes(env)
                    } else {
                        No
                    }
                }
                Val::App(Var::Builtin(Builtin::False), _, _, _) => {
                    if !x {
                        Yes(env)
                    } else {
                        No
                    }
                }
                _ => Maybe,
            },
            Pat::Or(x, y) => match x.match_with(val, env.clone(), mcxt, db) {
                Yes(env) => Yes(env),
                No => y.match_with(val, env, mcxt, db),
                Maybe => Maybe,
            },
            // TODO effects in the evaluator
            Pat::Eff(_, _, _) | Pat::EffRet(_) => Maybe,
        }
    }
}

/// `veffs` is empty if this is a `case` and not a `catch`.
// TODO: infer effects caught based on patterns
pub fn elab_case(
    value: Term,
    vspan: Span,
    val_ty: VTy,
    veffs: Vec<Val>,
    reason: ReasonExpected,
    cases: &[(Pre, Pre)],
    mut ret_ty: Option<(VTy, ReasonExpected)>,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<(Term, VTy), TypeError> {
    let state = mcxt.state();
    let mut rcases = Vec::new();
    let mut last_cov = if veffs.is_empty() {
        Cov::None
    } else {
        let effs: Vec<_> = veffs
            .iter()
            .filter_map(|x| match x {
                Val::App(Var::Builtin(Builtin::IO), _, _, _) => None,
                x => Some((x.clone(), Cov::None)),
            })
            .collect();
        if effs.is_empty() {
            return Err(TypeError::WrongCatchType(vspan, true));
        }
        Cov::Eff(Box::new(Cov::None), effs)
    };

    let mut first = true;
    for (pat, body) in cases {
        let pat = elab_pat(false, pat, &val_ty, &veffs, vspan, reason.clone(), mcxt, db)?;
        // If it doesn't already handle effects, wrap it in an `EffRet` pattern
        let pat = match pat {
            pat @ Pat::Eff(_, _, _) => pat,
            pat if !veffs.is_empty() => Pat::EffRet(Box::new(pat)),
            pat => pat,
        };
        let body = match &mut ret_ty {
            Some((ty, reason)) => {
                let term = check(body, &ty, reason.clone(), db, mcxt)?;
                // If the type we were given is a meta, the actual reason for future type errors is the type of the first branch
                if first {
                    if let Val::App(Var::Meta(_), _, _, _) = &ty {
                        *reason = ReasonExpected::MustMatch(body.span());
                    }
                }
                term
            }
            None => {
                let (term, ty) = infer(true, body, db, mcxt)?;
                ret_ty = Some((ty, ReasonExpected::MustMatch(body.span())));
                term
            }
        };
        first = false;

        mcxt.set_state(state.clone());
        let cov = last_cov
            .clone()
            .or(pat.cov(mcxt, db), mcxt, db)
            .simplify(&val_ty, db, mcxt);
        if cov == last_cov {
            // TODO real warnings
            eprintln!(
                "warning: redundant pattern '{}'",
                pat.pretty(db, &mut Names::new(mcxt.cxt, db)).ansi_string()
            );
        }
        last_cov = cov;

        rcases.push((pat, body));
    }

    if last_cov == Cov::All {
        let vty = val_ty.quote(mcxt.size, mcxt, db);
        let veffs = veffs
            .into_iter()
            .map(|x| x.quote(mcxt.size, mcxt, db))
            .collect();
        Ok((
            Term::Case(Box::new(value), Box::new(vty), rcases, veffs),
            ret_ty.unwrap().0,
        ))
    } else {
        Err(TypeError::Inexhaustive(vspan, last_cov, val_ty))
    }
}

pub fn elab_pat(
    in_eff: bool,
    pre: &Pre,
    ty: &VTy,
    effs: &[Val],
    vspan: Span,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<Pat, TypeError> {
    match &**pre {
        Pre_::EffPat(p, k) => {
            if effs.is_empty() {
                Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::EffPatternType(vspan, pre.span(), ty.clone(), Vec::new()),
                )))
            } else {
                // Use local unification to find the effect's return type
                mcxt.define(db.intern_name("_".into()), NameInfo::Local(Val::Type), db);
                let (var, vty) = mcxt.last_local(db).unwrap();
                let ret_ty = Val::App(var, Box::new(vty), Vec::new(), Glued::new());
                let p = elab_pat(true, p, &ret_ty, effs, vspan, reason.clone(), mcxt, db)?;
                let k = elab_pat(
                    true,
                    k,
                    &Val::Fun(Box::new(ret_ty), Box::new(ty.clone()), effs.to_vec()),
                    &[],
                    vspan,
                    reason,
                    mcxt,
                    db,
                )?;
                let eff = match &p {
                    Pat::Cons(_, ty, _) => (**ty).clone(),
                    // We want e.g. `_` to work if there's only one effect
                    _ if effs.len() == 1 => effs[0].clone(),
                    _ => panic!("Could not disambiguate which effect is matched by `eff` pattern; try using a constructor pattern"),
                };
                Ok(Pat::Eff(Box::new(eff), Box::new(p), Box::new(k)))
            }
        }
        Pre_::Lit(l) => match ty {
            Val::App(Var::Builtin(b), _, _, _) => match b {
                Builtin::I32 => Ok(Pat::Lit(*l, Width::W32)),
                Builtin::I64 => Ok(Pat::Lit(*l, Width::W64)),
                _ => Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::NotIntType(pre.span(), ty.clone().inline_metas(mcxt, db), reason),
                ))),
            },
            _ => Err(TypeError::InvalidPatternBecause(Box::new(
                TypeError::NotIntType(pre.span(), ty.clone().inline_metas(mcxt, db), reason),
            ))),
        },
        Pre_::Unit => {
            if unify(
                ty.clone(),
                Val::builtin(Builtin::UnitType, Val::Type),
                mcxt.size,
                pre.span(),
                db,
                mcxt,
            )? {
                // We just translate () into Pat::Any, since it's guaranteed to match anything of type ()
                Ok(Pat::Any)
            } else {
                Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::Unify(
                        mcxt.clone(),
                        pre.copy_span(Val::builtin(Builtin::UnitType, Val::Type)),
                        ty.clone(),
                        reason,
                    ),
                )))
            }
        }
        Pre_::Var(n) => {
            if let Ok((Var::Top(id), _)) = mcxt.lookup(*n, db) {
                if let Ok(info) = db.elaborate_def(id) {
                    match &*info.term {
                        Term::Var(Var::Cons(id2), _) | Term::Var(Var::Type(id2, _), _) => {
                            if id == *id2 {
                                // This is a constructor
                                return elab_pat_app(
                                    in_eff,
                                    pre,
                                    VecDeque::new(),
                                    ty,
                                    effs,
                                    vspan,
                                    reason,
                                    mcxt,
                                    db,
                                );
                            }
                        }
                        _ => (),
                    }
                }
            }
            if let Ok((Var::Builtin(b), _)) = mcxt.lookup(*n, db) {
                match b {
                    Builtin::True => {
                        if !unify(
                            ty.clone(),
                            Val::builtin(Builtin::Bool, Val::Type),
                            mcxt.size,
                            pre.span(),
                            db,
                            mcxt,
                        )
                        .map_err(|x| TypeError::InvalidPatternBecause(Box::new(x)))?
                        {
                            return Err(TypeError::InvalidPatternBecause(Box::new(
                                TypeError::Unify(
                                    mcxt.clone(),
                                    pre.copy_span(Val::builtin(Builtin::Bool, Val::Type)),
                                    ty.clone().inline_metas(mcxt, db),
                                    reason,
                                ),
                            )));
                        }
                        return Ok(Pat::Bool(true));
                    }
                    Builtin::False => {
                        if !unify(
                            ty.clone(),
                            Val::builtin(Builtin::Bool, Val::Type),
                            mcxt.size,
                            pre.span(),
                            db,
                            mcxt,
                        )
                        .map_err(|x| TypeError::InvalidPatternBecause(Box::new(x)))?
                        {
                            return Err(TypeError::InvalidPatternBecause(Box::new(
                                TypeError::Unify(
                                    mcxt.clone(),
                                    pre.copy_span(Val::builtin(Builtin::Bool, Val::Type)),
                                    ty.clone().inline_metas(mcxt, db),
                                    reason,
                                ),
                            )));
                        }
                        return Ok(Pat::Bool(false));
                    }
                    _ => (),
                }
            }
            mcxt.define(*n, NameInfo::Local(ty.clone()), db);
            Ok(Pat::Var(*n, Box::new(ty.clone())))
        }
        Pre_::Hole(MetaSource::Hole) => Ok(Pat::Any),
        Pre_::App(_, _, _) => {
            /// Find the head and spine of an application
            fn sep(pre: &Pre) -> (&Pre, VecDeque<(Icit, &Pre)>) {
                match &**pre {
                    Pre_::App(i, f, x) => {
                        let (head, mut spine) = sep(f);
                        spine.push_back((*i, x));
                        (head, spine)
                    }
                    _ => (pre, VecDeque::new()),
                }
            }
            let (head, spine) = sep(pre);

            elab_pat_app(in_eff, head, spine, ty, effs, vspan, reason, mcxt, db)
        }
        Pre_::Dot(head, member, spine) => elab_pat_app(
            in_eff,
            &pre.copy_span(Pre_::Dot(head.clone(), member.clone(), Vec::new())),
            spine.iter().map(|(i, x)| (*i, x)).collect(),
            ty,
            effs,
            vspan,
            reason,
            mcxt,
            db,
        ),
        Pre_::OrPat(x, y) => {
            let size_before = mcxt.size;
            // Use &[] for effs because we don't allow effect patterns in or patterns, for now
            let x = elab_pat(in_eff, x, ty, &[], vspan, reason.clone(), mcxt, db)?;
            if mcxt.size != size_before {
                todo!("error: for now we don't support capturing inside or-patterns")
            }
            let y = elab_pat(in_eff, y, ty, &[], vspan, reason, mcxt, db)?;
            if mcxt.size != size_before {
                todo!("error: for now we don't support capturing inside or-patterns")
            }

            Ok(Pat::Or(Box::new(x), Box::new(y)))
        }
        _ => Err(TypeError::InvalidPattern(pre.span())),
    }
}

fn elab_pat_app(
    in_eff: bool,
    head: &Pre,
    mut spine: VecDeque<(Icit, &Pre)>,
    expected_ty: &VTy,
    effs: &[Val],
    vspan: Span,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<Pat, TypeError> {
    let span = Span(
        head.span().0,
        spine.back().map(|(_, x)| x.span()).unwrap_or(head.span()).1,
    );

    let (term, fty) = infer(false, head, db, mcxt)?;
    let mut l = mcxt.size;
    let (id, fty, is_short_form) = match term.inline_top(db) {
        Term::Var(Var::Cons(id), _) => (id, fty, false),
        Term::Var(Var::Type(_, sid), _) => {
            let scope = db.lookup_intern_scope(sid);
            let m = db.intern_name(String::new());
            let mut found = None;
            let mut ty = fty;
            for &(n, v) in scope.iter() {
                if n == m {
                    ty = match db.elaborate_def(v) {
                        Ok(info) => info.typ.into_owned(),
                        Err(_) => return Ok(Pat::Any),
                    };
                    found = Some(v);
                    break;
                }
            }
            if let Some(f) = found {
                (f, ty, true)
            } else {
                return Err(TypeError::InvalidPattern(span));
            }
        }
        _ => return Err(TypeError::InvalidPattern(span)),
    };

    let fty = fty.inline_metas(mcxt, db);
    let mut eff_ret = None;

    let mut pspine = Vec::new();

    let arity = fty.arity(true);
    let f_arity = spine.iter().filter(|(i, _)| *i == Icit::Expl).count();
    let mut ty = fty.clone();

    // TODO unify constructor effects with given ones
    while let Some((i, pat)) = spine.pop_front() {
        match ty {
            Val::Pi(Icit::Impl, cl, mut effs) if i == Icit::Expl => {
                // Add an implicit argument to the pattern, and keep the explicit one on the stack
                spine.push_front((i, pat));
                mcxt.define(
                    db.intern_name("_".into()),
                    NameInfo::Local(cl.ty.clone()),
                    db,
                );
                pspine.push(Pat::Var(cl.name, Box::new(cl.ty.clone())));
                ty = cl.vquote(l.inc(), mcxt, db);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
                l = l.inc();
            }
            Val::Pi(i2, cl, mut effs) if i == i2 => {
                let pat = elab_pat(in_eff, pat, &cl.ty, &[], vspan, reason.clone(), mcxt, db)?;
                pspine.push(pat);
                ty = cl.vquote(l.inc(), mcxt, db);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
                l = l.inc();
            }
            Val::Fun(from, to, mut effs) if i == Icit::Expl => {
                let pat = elab_pat(in_eff, pat, &from, &[], vspan, reason.clone(), mcxt, db)?;
                pspine.push(pat);
                ty = *to;
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
            }
            _ => return Err(TypeError::WrongArity(head.copy_span(fty), arity, f_arity)),
        }
        unify_ret_type(
            ty.clone(),
            expected_ty,
            effs,
            vspan,
            span,
            &reason,
            mcxt,
            db,
        )?;
        ty = ty.inline_metas(mcxt, db);
    }

    // Apply any remaining implicits
    loop {
        match ty {
            Val::Pi(Icit::Impl, cl, mut effs) => {
                mcxt.define(
                    db.intern_name("_".into()),
                    NameInfo::Local(cl.ty.clone()),
                    db,
                );
                pspine.push(Pat::Var(cl.name, Box::new(cl.ty.clone())));
                ty = cl.vquote(l.inc(), mcxt, db);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
                l = l.inc();
            }
            ty2 => {
                // Put it back
                ty = ty2;
                break;
            }
        }
    }

    match &ty {
        Val::Fun(_, _, _) | Val::Pi(_, _, _) => {
            return Err(TypeError::WrongArity(head.copy_span(fty), arity, f_arity))
        }
        ty => {
            if let Some(eff_ret) = eff_ret {
                // First try to find an effect in `effs` that matches `rty`
                let mut found = false;
                for e in effs {
                    if let Ok(true) =
                        crate::elaborate::local_unify(ty.clone(), e.clone(), l, span, db, mcxt)
                    {
                        found = true;
                        break;
                    }
                }
                if !found {
                    return Err(TypeError::InvalidPatternBecause(Box::new(
                        TypeError::EffPatternType(vspan, span, ty.clone(), effs.to_vec()),
                    )));
                }

                // Now unify the expected type with the return type
                match crate::elaborate::local_unify(
                    eff_ret.clone(),
                    expected_ty.clone(),
                    l,
                    span,
                    db,
                    mcxt,
                ) {
                    Ok(true) => (),
                    Ok(false) => {
                        return Err(TypeError::InvalidPatternBecause(Box::new(
                            TypeError::Unify(
                                mcxt.clone(),
                                Spanned::new(eff_ret.clone().inline_metas(mcxt, db), span),
                                expected_ty.clone().inline_metas(mcxt, db),
                                reason,
                            ),
                        )))
                    }
                    Err(e) => return Err(TypeError::InvalidPatternBecause(Box::new(e))),
                }
            } else {
                // Unify with the expected type, for GADTs and constructors of different datatypes
                match crate::elaborate::local_unify(
                    ty.clone(),
                    expected_ty.clone(),
                    l,
                    span,
                    db,
                    mcxt,
                ) {
                    Ok(true) => (),
                    Ok(false) => {
                        return Err(TypeError::InvalidPatternBecause(Box::new(
                            TypeError::Unify(
                                mcxt.clone(),
                                Spanned::new(ty.clone().inline_metas(mcxt, db), span),
                                expected_ty.clone().inline_metas(mcxt, db),
                                reason,
                            ),
                        )))
                    }
                    Err(e) => return Err(TypeError::InvalidPatternBecause(Box::new(e))),
                }
            }
        }
    }

    let ty = ty.clone().inline_metas(mcxt, db);
    Ok(Pat::Cons(id, Box::new(ty), pspine))
}

fn unify_ret_type(
    fty: VTy,
    expected_ty: &VTy,
    effs: &[VTy],
    vspan: Span,
    span: Span,
    reason: &ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<(), TypeError> {
    let before_size = mcxt.size;

    let mut l = before_size;
    let mut rty = fty;
    let mut eff_ret = None;
    loop {
        match rty {
            Val::Pi(_, cl, mut effs) => {
                mcxt.define(
                    db.intern_name("_".into()),
                    NameInfo::Local(cl.ty.clone()),
                    db,
                );
                rty = cl.vquote(l.inc(), mcxt, db);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(rty);
                    rty = effs.pop().unwrap();
                    break;
                }
                l = l.inc();
            }
            Val::Fun(_, to, mut effs) => {
                rty = *to;
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(rty);
                    rty = effs.pop().unwrap();
                    break;
                }
            }
            _ => break,
        }
    }

    if let Some(eff_ret) = eff_ret {
        // First try to find an effect in `effs` that matches `rty`
        let mut found = false;
        for e in effs {
            if let Ok(true) =
                crate::elaborate::local_unify(rty.clone(), e.clone(), l, span, db, mcxt)
            {
                found = true;
                break;
            }
        }
        if !found {
            return Err(TypeError::InvalidPatternBecause(Box::new(
                TypeError::EffPatternType(vspan, span, rty.clone(), effs.to_vec()),
            )));
        }

        // Now unify the expected type with the return type
        match crate::elaborate::local_unify(eff_ret.clone(), expected_ty.clone(), l, span, db, mcxt)
        {
            Ok(true) => (),
            Ok(false) => {
                return Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::Unify(
                        mcxt.clone(),
                        Spanned::new(eff_ret.clone().inline_metas(mcxt, db), span),
                        expected_ty.clone().inline_metas(mcxt, db),
                        reason.clone(),
                    ),
                )))
            }
            Err(e) => return Err(TypeError::InvalidPatternBecause(Box::new(e))),
        }
    } else {
        // Unify with the expected type, for GADTs and constructors of different datatypes
        match crate::elaborate::local_unify(rty.clone(), expected_ty.clone(), l, span, db, mcxt) {
            Ok(true) => (),
            Ok(false) => {
                return Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::Unify(
                        mcxt.clone(),
                        Spanned::new(rty.clone().inline_metas(mcxt, db), span),
                        expected_ty.clone().inline_metas(mcxt, db),
                        reason.clone(),
                    ),
                )))
            }
            Err(e) => return Err(TypeError::InvalidPatternBecause(Box::new(e))),
        }
    }

    while mcxt.size != before_size {
        mcxt.undef(db);
    }
    Ok(())
}
