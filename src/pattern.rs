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
    /// eff p k
    Eff(Box<Pat>, Box<Pat>),
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
    Eff(Box<Cov>, Box<Cov>),
}
impl Cov {
    pub fn or(self, other: Self) -> Self {
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
                            .map(|(x, y)| x.or(y))
                            .collect();
                    } else {
                        v.push((cons, cov));
                    }
                }
                Cov::Cons(v)
            }
            (Cov::Eff(mut a, mut b), Cov::Eff(a2, b2)) => {
                *a = a.or(*a2);
                *b = b.or(*b2);
                Cov::Eff(a, b)
            }
            _ => unreachable!(),
        }
    }

    pub fn pretty_rest(&self, ty: &VTy, db: &dyn Compiler, mcxt: &MCxt) -> Doc {
        println!("Prettying {:?}", self);
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
                let (var, vty) = mcxt.last_local(db).unwrap();
                let cont_ty = Val::App(var, Box::new(vty), Vec::new(), Glued::new());

                let (sid, ty) = match ty {
                    Val::App(Var::Type(_, sid), _, _, _) => (*sid, ty.clone()),
                    Val::With(_, effs) if effs.len() == 1 => {
                        match effs[0].clone().inline(mcxt.size, db, &mcxt) {
                            // The actual return type of the term doesn't matter, the constructor can have a different one
                            // So we use a local here, like we did when elaborating the pattern
                            Val::App(Var::Type(_, sid), _, _, _) => (sid, Val::With(Box::new(cont_ty), effs.clone())),
                            _ => panic!(
                                "Called Cov::pretty_rest() on a Cov::Cons but passed non-datatype {:?}",
                                ty
                            ),
                        }
                    }
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
                                    .ret_type(mcxt.size, &mcxt, db);
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
                                Val::Fun(from, to) => {
                                    cons_ty = *to;
                                    *from
                                }
                                Val::Pi(_, cl) => {
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
                            Val::Fun(from, to) => {
                                cons_ty = *to;
                                *from
                            }
                            Val::Pi(_, to) => {
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
            Cov::Eff(a, b) => {
                let base_ty = match ty {
                    Val::With(ty, _) => ty,
                    _ => unreachable!(),
                };
                let mut d = None;
                if !matches!(&**a, Cov::All) {
                    d = Some(a.pretty_rest(base_ty, db, mcxt));
                }
                if !matches!(&**b, Cov::All) {
                    d = Some(match d {
                        Some(d) => d.add(" | ").chain(
                            Doc::keyword("eff")
                                .space()
                                .chain(b.pretty_rest(ty, db, mcxt).nest(Prec::Atom))
                                .add(" _"),
                        ),
                        None => Doc::keyword("eff")
                            .space()
                            .chain(b.pretty_rest(ty, db, mcxt).nest(Prec::Atom))
                            .add(" _"),
                    });
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
                let (var, vty) = mcxt.last_local(db).unwrap();
                let cont_ty = Val::App(var, Box::new(vty), Vec::new(), Glued::new());

                let (sid, ty) = match ty {
                    Val::App(Var::Type(_, sid), _, _, _) => (*sid, ty.clone()),
                    Val::With(_, effs) if effs.len() == 1 => {
                        match effs[0].clone().inline(mcxt.size, db, &mcxt) {
                            // The actual return type of the term doesn't matter, the constructor can have a different one
                            // So we use a local here, like we did when elaborating the pattern
                            Val::App(Var::Type(_, sid), _, _, _) => (sid, Val::With(Box::new(cont_ty), effs.clone())),
                            _ => panic!(
                                "Called Cov::simplify() on a Cov::Cons but passed non-datatype {:?}",
                                ty
                            ),
                        }
                    }
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
                                    .ret_type(mcxt.size, &mcxt, db);
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
                        .clone();
                    let mut l = mcxt.size;

                    for x in std::mem::take(args) {
                        let ty = match cons_ty {
                            Val::Fun(from, to) => {
                                cons_ty = *to;
                                *from
                            }
                            Val::Pi(_, cl) => {
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
            Cov::Eff(mut a, mut b) => {
                let base_ty = match ty {
                    Val::With(ty, _) => ty,
                    _ => unreachable!(),
                };
                *a = a.simplify(base_ty, db, mcxt);
                *b = b.simplify(ty, db, mcxt);
                if matches!((&*a, &*b), (Cov::All, Cov::All)) {
                    Cov::All
                } else {
                    Cov::Eff(a, b)
                }
            }
        }
    }
}

pub enum MatchResult {
    Yes(Env),
    No,
    Maybe,
}

impl Pat {
    pub fn cov(&self) -> Cov {
        match self {
            Pat::Any => Cov::All,
            Pat::Var(_, _) => Cov::All,
            Pat::Cons(id, _, v) => Cov::Cons(vec![(*id, v.into_iter().map(Pat::cov).collect())]),
            Pat::Or(x, y) => x.cov().or(y.cov()),
            Pat::Lit(l, _) => Cov::Lit(std::iter::once(l.to_usize()).collect()),
            Pat::Bool(b) => Cov::Bool(*b),
            Pat::Eff(p, k) => {
                assert_eq!(k.cov(), Cov::All);
                Cov::Eff(Box::new(Cov::None), Box::new(p.cov()))
            }
            Pat::EffRet(p) => Cov::Eff(Box::new(p.cov()), Box::new(Cov::None)),
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
                p.iter()
                    .map(|x| Doc::none().space().chain(x.pretty(db, names))),
                Doc::none(),
            )),
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
            Pat::Eff(p, k) => {
                names.add(names.hole_name());
                Doc::keyword("eff")
                    .space()
                    .chain(p.pretty(db, names))
                    .space()
                    .chain(k.pretty(db, names))
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
                ()
            }
            Pat::Eff(p, k) => {
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
            Pat::Eff(p, k) => {
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
            Pat::Eff(mut p, mut k) => {
                env.push(None);
                *l = l.inc();
                *p = p.eval_quote(env, l, mcxt, db);
                *k = k.eval_quote(env, l, mcxt, db);
                Pat::Eff(p, k)
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
            Pat::Eff(_, _) | Pat::EffRet(_) => Maybe,
        }
    }
}

pub fn elab_case(
    value: Term,
    vspan: Span,
    val_ty: VTy,
    reason: ReasonExpected,
    cases: &[(Pre, Pre)],
    mut ret_ty: Option<(VTy, ReasonExpected)>,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<(Term, VTy), TypeError> {
    let state = mcxt.state();
    let mut rcases = Vec::new();
    let mut last_cov = Cov::None;

    let mut first = true;
    for (pat, body) in cases {
        let pat = elab_pat(false, pat, &val_ty, vspan, reason.clone(), mcxt, db)?;
        let pat = match (pat, &val_ty) {
            (pat @ Pat::Eff(_, _), _) => pat,
            (pat, Val::With(_, _)) => Pat::EffRet(Box::new(pat)),
            (pat, _) => pat,
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
        let cov = last_cov.clone().or(pat.cov()).simplify(&val_ty, db, mcxt);
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
        Ok((
            Term::Case(Box::new(value), Box::new(vty), rcases),
            ret_ty.unwrap().0,
        ))
    } else {
        Err(TypeError::Inexhaustive(vspan, last_cov, val_ty))
    }
}

pub fn elab_pat(
    in_eff: bool,
    pre: &Pre,
    pty: &VTy,
    vspan: Span,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<Pat, TypeError> {
    let (ty, effs) = match pty {
        Val::With(ty, effs) if !in_eff => (&**ty, effs.clone()),
        ty => (ty, Vec::new()),
    };
    match &**pre {
        Pre_::EffPat(p, k) => {
            if effs.len() > 1 {
                todo!("What if there's more than one effect?");
            }

            if effs.is_empty() {
                Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::EffPatternType(vspan, pre.span(), pty.clone()),
                )))
            } else {
                // Use local unification to find the effect's return type
                mcxt.define(db.intern_name("_".into()), NameInfo::Local(Val::Type), db);
                let (var, vty) = mcxt.last_local(db).unwrap();
                let ret_ty = Val::App(var, Box::new(vty), Vec::new(), Glued::new());
                let p = elab_pat(
                    true,
                    p,
                    &Val::With(Box::new(ret_ty.clone()), vec![effs[0].clone()]),
                    vspan,
                    reason.clone(),
                    mcxt,
                    db,
                )?;
                let k = elab_pat(
                    true,
                    k,
                    &Val::Fun(Box::new(ret_ty), Box::new(pty.clone())),
                    vspan,
                    reason,
                    mcxt,
                    db,
                )?;
                Ok(Pat::Eff(Box::new(p), Box::new(k)))
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
        Pre_::Unit => match ty {
            // We just translate () into Pat::Any, since it's guaranteed to match anything of type ()
            Val::App(Var::Builtin(Builtin::UnitType), _, _, _) => Ok(Pat::Any),
            _ => Err(TypeError::InvalidPatternBecause(Box::new(
                TypeError::Unify(
                    mcxt.clone(),
                    pre.copy_span(Val::builtin(Builtin::UnitType, Val::Type)),
                    ty.clone(),
                    reason,
                ),
            ))),
        },
        Pre_::Var(n) => {
            if let Ok((Var::Top(id), _)) = mcxt.lookup(*n, db) {
                if let Ok(info) = db.elaborate_def(id) {
                    if let Term::Var(Var::Cons(id2), _) = &*info.term {
                        if id == *id2 {
                            // This is a constructor
                            return elab_pat_app(
                                in_eff,
                                pre,
                                VecDeque::new(),
                                ty,
                                vspan,
                                reason,
                                mcxt,
                                db,
                            );
                        }
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

            elab_pat_app(in_eff, head, spine, ty, vspan, reason, mcxt, db)
        }
        Pre_::Dot(head, member, spine) => elab_pat_app(
            in_eff,
            &pre.copy_span(Pre_::Dot(head.clone(), member.clone(), Vec::new())),
            spine.iter().map(|(i, x)| (*i, x)).collect(),
            ty,
            vspan,
            reason,
            mcxt,
            db,
        ),
        Pre_::OrPat(x, y) => {
            let size_before = mcxt.size;
            let x = elab_pat(in_eff, x, ty, vspan, reason.clone(), mcxt, db)?;
            if mcxt.size != size_before {
                todo!("error: for now we don't support capturing inside or-patterns")
            }
            let y = elab_pat(in_eff, y, ty, vspan, reason, mcxt, db)?;
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
    vspan: Span,
    reason: ReasonExpected,
    mcxt: &mut MCxt,
    db: &dyn Compiler,
) -> Result<Pat, TypeError> {
    let span = Span(
        head.span().0,
        spine.back().map(|(_, x)| x.span()).unwrap_or(head.span()).1,
    );

    let (term, mut ty) = infer(false, head, db, mcxt)?;
    let mut l = mcxt.size;
    match term.inline_top(db) {
        Term::Var(Var::Cons(id), _) => {
            let mut pspine = Vec::new();

            let arity = ty.arity(true);
            let f_arity = spine.iter().filter(|(i, _)| *i == Icit::Expl).count();

            while let Some((i, pat)) = spine.pop_front() {
                match ty {
                    Val::Pi(Icit::Impl, cl) if i == Icit::Expl => {
                        // Add an implicit argument to the pattern, and keep the explicit one on the stack
                        spine.push_front((i, pat));
                        mcxt.define(
                            db.intern_name("_".into()),
                            NameInfo::Local(cl.ty.clone()),
                            db,
                        );
                        pspine.push(Pat::Var(cl.name, Box::new(cl.ty.clone())));
                        ty = cl.vquote(l.inc(), mcxt, db);
                        l = l.inc();
                    }
                    Val::Pi(i2, cl) if i == i2 => {
                        let pat = elab_pat(in_eff, pat, &cl.ty, vspan, reason.clone(), mcxt, db)?;
                        pspine.push(pat);
                        ty = cl.vquote(l.inc(), mcxt, db);
                        l = l.inc();
                    }
                    Val::Fun(from, to) if i == Icit::Expl => {
                        let pat = elab_pat(in_eff, pat, &from, vspan, reason.clone(), mcxt, db)?;
                        pspine.push(pat);
                        ty = *to;
                    }
                    _ => return Err(TypeError::WrongNumConsArgs(span, arity, f_arity)),
                }
            }

            // Apply any remaining implicits
            loop {
                match ty {
                    Val::Pi(Icit::Impl, cl) => {
                        mcxt.define(
                            db.intern_name("_".into()),
                            NameInfo::Local(cl.ty.clone()),
                            db,
                        );
                        pspine.push(Pat::Var(cl.name, Box::new(cl.ty.clone())));
                        ty = cl.vquote(l.inc(), mcxt, db);
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
                Val::Fun(_, _) | Val::Pi(_, _) => {
                    return Err(TypeError::WrongNumConsArgs(span, arity, f_arity))
                }
                ty => {
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

            Ok(Pat::Cons(id, Box::new(expected_ty.clone()), pspine))
        }
        _ => Err(TypeError::InvalidPattern(span)),
    }
}
