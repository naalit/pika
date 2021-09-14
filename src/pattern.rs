use crate::common::*;
use crate::elaborate::*;
use crate::term::*;
use durin::ir::{Signed, Width};

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Pat {
    Any,
    Var(Name, Box<Ty>),
    Cons(DefId, Box<Ty>, Vec<(Option<(Name, Ty)>, Pat)>),
    Or(Box<Pat>, Box<Pat>),
    Lit(Literal, Width, Signed),
    Bool(bool),
    /// eff p k :: E
    Eff(Box<Term>, Box<Pat>, Box<Pat>),
    EffRet(Box<Pat>),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Cov {
    /// We covered everything, there's nothing left
    All,
    /// We didn't cover anything yet
    None,
    /// We *did* cover these constructors
    Cons(Vec<(DefId, Vec<Cov>)>),
    /// We *did* cover these literals
    Lit(HashSet<Literal>),
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
    pub fn or(self, other: Self, mcxt: &MCxt) -> Self {
        match (self, other) {
            (Cov::All, _) | (_, Cov::All) => Cov::All,
            (Cov::None, x) | (x, Cov::None) => x,
            (Cov::Bool(x), Cov::Bool(y)) if x != y => Cov::All,
            (Cov::Bool(x), Cov::Bool(_)) => Cov::Bool(x),
            (Cov::Lit(mut a), Cov::Lit(b)) => {
                a.extend(b);
                Cov::Lit(a)
            }
            (Cov::Cons(mut v), Cov::Cons(v2)) => {
                for (cons, cov) in v2 {
                    if let Some((_, cov2)) = v.iter_mut().find(|(c, _)| *c == cons) {
                        *cov2 = std::mem::take(cov2)
                            .into_iter()
                            .zip(cov)
                            .map(|(x, y)| x.or(y, mcxt))
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
                            &mut mcxt.clone(),
                        )
                        .unwrap_or(false)
                    }) {
                        *cov2 = cov2.take().or(cov, mcxt);
                    } else {
                        v.push((eff, cov));
                    }
                }
                *a = a.or(*a2, mcxt);
                Cov::Eff(a, v)
            }
            _ => unreachable!(),
        }
    }

    pub fn pretty_rest(&self, ty: &VTy, mcxt: &MCxt) -> Doc {
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
                mcxt.define(mcxt.db.intern_name("_".into()), NameInfo::Local(Val::Type));

                let ty = ty.clone().inline(mcxt.size, &mcxt);
                let sid = match &ty {
                    Val::App(Var::Type(_, sid), _, _, _) => *sid,
                    _ => panic!(
                        "Called Cov::pretty_rest() on a Cov::Cons but passed non-datatype {:?}",
                        ty
                    ),
                };

                let mut v = Vec::new();
                let mut unmatched: Vec<DefId> = mcxt
                    .db
                    .lookup_intern_scope(sid)
                    .iter()
                    .filter_map(|&(_name, id)| {
                        let info = mcxt.db.elaborate_def(id).ok()?;
                        match &**info.term.as_ref().unwrap() {
                            Term::Var(Var::Cons(cid), _) if id == *cid => {
                                let mut size = mcxt.size;
                                let cty = IntoOwned::<Val>::into_owned(info.typ)
                                    .cons_ret_type(&mut size, &mcxt);
                                if crate::elaborate::local_unify(
                                    cty,
                                    ty.clone(),
                                    size,
                                    Span::empty(),
                                    &mut mcxt.clone(),
                                )
                                .ok()?
                                {
                                    Some(id)
                                } else {
                                    println!(
                                        "Skipping constructor {}",
                                        info.term
                                            .as_ref()
                                            .unwrap()
                                            .pretty(mcxt.db, &mut Names::new(mcxt.cxt, mcxt.db))
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
                        let (pre, _) = mcxt.db.lookup_intern_def(*cons);
                        let pre = mcxt.db.lookup_intern_predef(pre);
                        let name = pre.name().unwrap();

                        let mut cons_ty = (*mcxt
                            .db
                            .elaborate_def(*cons)
                            .expect("probably an invalid constructor?")
                            .typ)
                            .clone();
                        let mut l = mcxt.size;

                        let mut v2 = vec![Doc::start(name.get(mcxt.db))];
                        for x in args {
                            let ty = match cons_ty {
                                // TODO effect constructors
                                Val::Fun(from, to, _) => {
                                    cons_ty = *to;
                                    *from
                                }
                                Val::Clos(Pi, _, cl, _) => {
                                    let from = cl.ty.clone();
                                    cons_ty = cl.vquote(l, &mcxt);
                                    l = l.inc();
                                    from
                                }
                                _ => unreachable!(),
                            };
                            v2.push(x.pretty_rest(&ty, &mcxt));
                        }

                        v.push(Doc::intersperse(v2, Doc::none().space()));
                    }
                }

                for cons in unmatched {
                    let (pre, _) = mcxt.db.lookup_intern_def(cons);
                    let pre = mcxt.db.lookup_intern_predef(pre);
                    let name = pre.name().unwrap();

                    let mut cons_ty = (*mcxt
                        .db
                        .elaborate_def(cons)
                        .expect("probably an invalid constructor?")
                        .typ)
                        .clone();
                    let mut l = mcxt.size;

                    let mut v2 = vec![Doc::start(name.get(mcxt.db))];
                    loop {
                        let from = match cons_ty {
                            // TODO effect constructors
                            Val::Fun(from, to, _) => {
                                cons_ty = *to;
                                *from
                            }
                            Val::Clos(Pi, _, to, _) => {
                                let from = to.ty.clone();
                                cons_ty = to.vquote(l, &mcxt);
                                l = l.inc();
                                from
                            }
                            _ => break,
                        };
                        v2.push(Cov::None.pretty_rest(&from, &mcxt));
                    }

                    v.push(Doc::intersperse(v2, Doc::none().space()));
                }

                Doc::intersperse(v, Doc::start(" | "))
            }
            Cov::Eff(a, v) => {
                let mut d = None;
                if !matches!(&**a, Cov::All) {
                    d = Some(a.pretty_rest(ty, mcxt));
                }
                for (e, c) in v {
                    if !matches!(c, Cov::All) {
                        d = Some(match d {
                            Some(d) => d.add(" | ").chain(
                                Doc::keyword("eff")
                                    .space()
                                    .chain(c.pretty_rest(&e, mcxt).nest(Prec::Atom))
                                    .add(" _"),
                            ),
                            None => Doc::keyword("eff")
                                .space()
                                .chain(c.pretty_rest(e, mcxt).nest(Prec::Atom))
                                .add(" _"),
                        });
                    }
                }
                d.expect("Empty Cov::Eff")
            }
        }
    }

    pub fn simplify(self, ty: &VTy, mcxt: &MCxt) -> Self {
        match self {
            Cov::All => Cov::All,
            Cov::None => Cov::None,
            Cov::Lit(s) => Cov::Lit(s),
            Cov::Bool(x) => Cov::Bool(x),
            Cov::Cons(mut covs) => {
                let mut mcxt = mcxt.clone();
                mcxt.define(mcxt.db.intern_name("_".into()), NameInfo::Local(Val::Type));

                let ty = ty.clone().inline(mcxt.size, &mcxt);
                let sid = match &ty {
                    Val::App(Var::Type(_, sid), _, _, _) => *sid,
                    _ => panic!(
                        "Called Cov::simplify() on a Cov::Cons but passed non-datatype {:?}",
                        ty
                    ),
                };
                // Store the function type specialized to the context
                let state = mcxt.state();
                let mut unmatched: Vec<(DefId, Val)> = mcxt
                    .db
                    .lookup_intern_scope(sid)
                    .iter()
                    .filter_map(|&(_name, id)| {
                        let info = mcxt.db.elaborate_def(id).ok()?;
                        match &**info.term.as_ref().unwrap() {
                            Term::Var(Var::Cons(cid), _) if id == *cid => {
                                let cty = info.typ.into_owned();
                                if let Ok(cty) =
                                    UnifyRetType::no_effects(cty, &ty, &mut mcxt).unify_ret_type()
                                {
                                    // Make sure local constraints aren't applied to other constructors
                                    mcxt.set_state(state.clone());
                                    Some((id, cty))
                                } else {
                                    eprintln!(
                                        "Skipping constructor {}",
                                        info.term
                                            .as_ref()
                                            .unwrap()
                                            .pretty(mcxt.db, &mut Names::new(mcxt.cxt, mcxt.db))
                                            .ansi_string()
                                    );
                                    mcxt.set_state(state.clone());
                                    None
                                }
                            }
                            _ => None,
                        }
                    })
                    .collect();
                for (cons, args) in &mut covs {
                    // We'll use the local constraints from this constructor to inline metas on the argument types
                    let (_, mut cons_ty) = unmatched
                        .iter_mut()
                        .find(|(id, _)| id == cons)
                        .unwrap()
                        .clone();

                    let mut l = mcxt.size;

                    for x in std::mem::take(args) {
                        let ty = match cons_ty {
                            // TODO effect constructors
                            Val::Fun(from, to, _) => {
                                cons_ty = *to;
                                *from
                            }
                            Val::Clos(Pi, _, cl, _) => {
                                let from = cl.ty.clone();
                                cons_ty = cl.vquote(l, &mcxt);
                                l = l.inc();
                                from
                            }
                            _ => unreachable!(),
                        };
                        args.push(x.simplify(&ty, &mcxt));
                    }

                    if args.iter().all(|x| *x == Cov::All) {
                        // This pattern is guaranteed to cover this constructor completely
                        unmatched.retain(|(id, _)| id != cons);
                    }
                }

                if unmatched.is_empty() {
                    Cov::All
                } else {
                    Cov::Cons(covs)
                }
            }
            Cov::Eff(mut a, mut v) => {
                *a = a.simplify(ty, mcxt);
                let mut all_all = true;
                for (e, c) in &mut v {
                    *c = c.take().simplify(&e, mcxt);
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
    pub fn cov(&self, mcxt: &MCxt) -> Cov {
        match self {
            Pat::Any => Cov::All,
            Pat::Var(_, _) => Cov::All,
            Pat::Cons(id, _, v) => {
                Cov::Cons(vec![(*id, v.iter().map(|(_, x)| x.cov(mcxt)).collect())])
            }
            Pat::Or(x, y) => x.cov(mcxt).or(y.cov(mcxt), mcxt),
            Pat::Lit(l, _, _) => Cov::Lit(std::iter::once(*l).collect()),
            Pat::Bool(b) => Cov::Bool(*b),
            Pat::Eff(e, p, k) => {
                assert_eq!(k.cov(mcxt), Cov::All);
                // TODO Cov can have a lifetime tied to its Pat and borrow the Val
                Cov::Eff(
                    Box::new(Cov::None),
                    vec![((**e).clone().evaluate(&mcxt.env(), mcxt), p.cov(mcxt))],
                )
            }
            Pat::EffRet(p) => Cov::Eff(Box::new(p.cov(mcxt)), Vec::new()),
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
            Pat::Cons(id, ty, p) => Doc::start(
                db.lookup_intern_predef(db.lookup_intern_def(*id).0)
                    .name()
                    .unwrap()
                    .get(db),
            )
            .add(": ")
            .chain(ty.pretty(db, names))
            .add(" @ ")
            .chain(Doc::intersperse(
                p.iter().map(|(v, x)| {
                    if let Some((n, _)) = v {
                        names.add(*n);
                    }
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
            Pat::Lit(x, _, _) => x.pretty(db),
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

    pub fn add_names(&self, size: Size, names: &mut Names) -> Size {
        match self {
            Pat::Any | Pat::Lit(_, _, _) | Pat::Bool(_) => size,
            Pat::Var(n, _) => {
                names.add(*n);
                size.inc()
            }
            Pat::Cons(_, _, v) => v.iter().fold(size, |size, (v, p)| {
                let size = if let Some((n, _)) = v {
                    names.add(*n);
                    size.inc()
                } else {
                    size
                };
                p.add_names(size, names)
            }),
            Pat::Or(_, _) => size,
            Pat::Eff(_, p, k) => {
                // A hidden local for the effect return type
                names.add(names.hole_name());
                let size = p.add_names(size.inc(), names);
                k.add_names(size, names)
            }
            Pat::EffRet(p) => p.add_names(size, names),
        }
    }

    pub fn eval_quote(self, env: &mut Env, at: &mut Size, mcxt: &MCxt) -> Self {
        match self {
            Pat::Any => Pat::Any,
            Pat::Var(n, mut ty) => {
                let vty = ty.clone().evaluate(env, mcxt);
                *ty = ty.eval_quote(env, *at, mcxt);

                env.push(Some(Val::local(at.next_lvl(), vty)));
                *at = at.inc();

                Pat::Var(n, ty)
            }
            Pat::Cons(x, mut ty, y) => {
                *ty = ty.eval_quote(env, *at, mcxt);
                Pat::Cons(
                    x,
                    ty,
                    y.into_iter()
                        .map(|(v, p)| {
                            let v = v.map(|(n, t)| {
                                let vty = t.clone().evaluate(env, mcxt);
                                let t = t.eval_quote(env, *at, mcxt);

                                env.push(Some(Val::local(at.next_lvl(), vty)));
                                *at = at.inc();

                                (n, t)
                            });
                            (v, p.eval_quote(env, at, mcxt))
                        })
                        .collect(),
                )
            }
            Pat::Or(mut x, mut y) => {
                *x = x.eval_quote(env, at, mcxt);
                *y = y.eval_quote(env, at, mcxt);
                Pat::Or(x, y)
            }
            Pat::Lit(x, w, s) => Pat::Lit(x, w, s),
            Pat::Bool(x) => Pat::Bool(x),
            Pat::Eff(mut e, mut p, mut k) => {
                *e = e.eval_quote(env, *at, mcxt);
                env.push(Some(Val::local(at.next_lvl(), Val::Type)));
                *at = at.inc();
                *p = p.eval_quote(env, at, mcxt);
                *k = k.eval_quote(env, at, mcxt);
                Pat::Eff(e, p, k)
            }
            Pat::EffRet(mut x) => {
                *x = x.eval_quote(env, at, mcxt);
                Pat::EffRet(x)
            }
        }
    }

    pub fn match_with(&self, val: &Val, mut env: Env, mcxt: &MCxt) -> MatchResult {
        use MatchResult::*;
        match self {
            Pat::Any => Yes(env),
            Pat::Var(_, _) => {
                env.push(Some(val.clone()));
                Yes(env)
            }
            Pat::Cons(id, _, v) => match val.clone().inline(env.size, mcxt) {
                Val::App(Var::Cons(id2), _, sp, _) => {
                    if *id == id2 {
                        let mut any_maybe = false;
                        for ((v, i), elim) in v.iter().zip(&sp) {
                            let val = match elim {
                                Elim::App(_, v) => v,
                                _ => unreachable!(),
                            };
                            let mut e2 = env.clone();
                            if v.is_some() {
                                e2.push(Some(val.clone()));
                            }
                            match i.match_with(val, e2, mcxt) {
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
            Pat::Lit(x, _, _) => match val.unarc() {
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
            Pat::Or(x, y) => match x.match_with(val, env.clone(), mcxt) {
                Yes(env) => Yes(env),
                No => y.match_with(val, env, mcxt),
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
        let pat = elab_pat(
            false,
            pat,
            &val_ty,
            &veffs,
            vspan,
            reason.clone(),
            ret_ty.as_ref().map(|x| &x.0),
            mcxt,
        )?;
        // If it doesn't already handle effects, wrap it in an `EffRet` pattern
        let pat = match pat {
            pat @ Pat::Eff(_, _, _) => pat,
            pat if !veffs.is_empty() => Pat::EffRet(Box::new(pat)),
            pat => pat,
        };
        let body = match &mut ret_ty {
            Some((ty, reason)) => {
                let term = check(body, &ty, reason.clone(), mcxt)?;
                // If the type we were given is a meta, the actual reason for future type errors is the type of the first branch
                if first {
                    if let Val::App(Var::Meta(_), _, _, _) = &ty {
                        *reason = ReasonExpected::MustMatch(body.span());
                    }
                }
                term
            }
            None => {
                let (term, ty) = infer(true, body, mcxt)?;
                ret_ty = Some((ty, ReasonExpected::MustMatch(body.span())));
                term
            }
        };
        first = false;

        mcxt.set_state(state.clone());
        let cov = last_cov
            .clone()
            .or(pat.cov(mcxt), mcxt)
            .simplify(&val_ty, mcxt);
        if cov == last_cov {
            // TODO real warnings
            eprintln!(
                "warning: redundant pattern '{}'",
                pat.pretty(mcxt.db, &mut Names::new(mcxt.cxt, mcxt.db))
                    .ansi_string()
            );
        }
        last_cov = cov;

        rcases.push((pat, body));
    }

    if last_cov == Cov::All {
        let vty = val_ty.quote(mcxt.size, mcxt);
        let veffs = veffs
            .into_iter()
            .map(|x| x.quote(mcxt.size, mcxt))
            .collect();
        let ret_ty = ret_ty.unwrap().0;
        let tret_ty = ret_ty.clone().quote(mcxt.size, mcxt);
        Ok((
            Term::Case(
                Box::new(value),
                Box::new(vty),
                rcases,
                veffs,
                Box::new(tret_ty),
            ),
            ret_ty,
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
    body_ret_ty: Option<&VTy>,
    mcxt: &mut MCxt,
) -> Result<Pat, TypeError> {
    match &**pre {
        Pre_::EffPat(p, k) => {
            if effs.is_empty() {
                Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::EffPatternType(vspan, pre.span(), ty.clone(), Vec::new()),
                )))
            } else {
                // Use local unification to find the effect's return type
                let before_size = mcxt.size;
                mcxt.define(mcxt.db.intern_name("_".into()), NameInfo::Local(Val::Type));
                let (var, vty) = mcxt.last_local().unwrap();
                let ret_ty = Val::App(var, Box::new(vty), Vec::new(), Glued::new());
                let p = elab_pat(
                    true,
                    p,
                    &ret_ty,
                    effs,
                    vspan,
                    reason.clone(),
                    body_ret_ty,
                    mcxt,
                )?;
                let k = elab_pat(
                    true,
                    k,
                    &Val::Fun(
                        Box::new(ret_ty),
                        Box::new(body_ret_ty.unwrap().clone()),
                        Vec::new(),
                    ),
                    &[],
                    vspan,
                    reason,
                    body_ret_ty,
                    mcxt,
                )?;
                let eff = match &p {
                    Pat::Cons(_, ty, _) => (**ty).clone().eval_quote(&mut Env::new(before_size.inc()), before_size, mcxt),
                    // We want e.g. `_` to work if there's only one effect
                    _ if effs.len() == 1 => effs[0].clone().quote(before_size, mcxt),
                    _ => panic!("Could not disambiguate which effect is matched by `eff` pattern; try using a constructor pattern"),
                };
                Ok(Pat::Eff(Box::new(eff), Box::new(p), Box::new(k)))
            }
        }
        Pre_::Lit(l) => match ty {
            Val::App(Var::Builtin(b), _, _, _) => match b {
                Builtin::I32 => Ok(Pat::Lit(*l, Width::W32, true)),
                Builtin::I64 => Ok(Pat::Lit(*l, Width::W64, true)),
                _ => Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::NotIntType(
                        pre.span(),
                        ty.clone().inline_metas(mcxt.size, mcxt),
                        reason,
                    ),
                ))),
            },
            _ => Err(TypeError::InvalidPatternBecause(Box::new(
                TypeError::NotIntType(pre.span(), ty.clone().inline_metas(mcxt.size, mcxt), reason),
            ))),
        },
        Pre_::Unit => {
            if unify(
                ty.clone(),
                Val::builtin(Builtin::UnitType, Val::Type),
                mcxt.size,
                pre.span(),
                mcxt,
            )? {
                // We just translate () into Pat::Any, since it's guaranteed to match anything of type ()
                Ok(Pat::Any)
            } else {
                Err(TypeError::InvalidPatternBecause(Box::new(
                    TypeError::Unify(
                        pre.copy_span(Val::builtin(Builtin::UnitType, Val::Type)),
                        ty.clone(),
                        reason,
                    ),
                )))
            }
        }
        Pre_::Var(n) => {
            if let Ok((Var::Top(id), _)) = mcxt.lookup(*n) {
                if let Some(term) = mcxt.def_term(id) {
                    match term {
                        Term::Var(Var::Cons(id2), _) | Term::Var(Var::Type(id2, _), _) => {
                            if id == id2 {
                                // This is a constructor
                                return elab_pat_app(
                                    in_eff,
                                    pre,
                                    VecDeque::new(),
                                    ty,
                                    effs,
                                    vspan,
                                    reason,
                                    body_ret_ty,
                                    mcxt,
                                );
                            }
                        }
                        _ => (),
                    }
                }
            }
            if let Ok((Var::Builtin(b), _)) = mcxt.lookup(*n) {
                match b {
                    Builtin::True => {
                        if !unify(
                            ty.clone(),
                            Val::builtin(Builtin::Bool, Val::Type),
                            mcxt.size,
                            pre.span(),
                            mcxt,
                        )
                        .map_err(|x| TypeError::InvalidPatternBecause(Box::new(x)))?
                        {
                            return Err(TypeError::InvalidPatternBecause(Box::new(
                                TypeError::Unify(
                                    pre.copy_span(Val::builtin(Builtin::Bool, Val::Type)),
                                    ty.clone().inline_metas(mcxt.size, mcxt),
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
                            mcxt,
                        )
                        .map_err(|x| TypeError::InvalidPatternBecause(Box::new(x)))?
                        {
                            return Err(TypeError::InvalidPatternBecause(Box::new(
                                TypeError::Unify(
                                    pre.copy_span(Val::builtin(Builtin::Bool, Val::Type)),
                                    ty.clone().inline_metas(mcxt.size, mcxt),
                                    reason,
                                ),
                            )));
                        }
                        return Ok(Pat::Bool(false));
                    }
                    _ => (),
                }
            }
            mcxt.define(*n, NameInfo::Local(ty.clone()));
            Ok(Pat::Var(
                *n,
                Box::new(ty.clone().quote(mcxt.size.dec(), mcxt)),
            ))
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

            elab_pat_app(
                in_eff,
                head,
                spine,
                ty,
                effs,
                vspan,
                reason,
                body_ret_ty,
                mcxt,
            )
        }
        Pre_::Dot(_, _) => elab_pat_app(
            in_eff,
            &pre,
            VecDeque::new(),
            ty,
            effs,
            vspan,
            reason,
            body_ret_ty,
            mcxt,
        ),
        Pre_::OrPat(x, y) => {
            let size_before = mcxt.size;
            // Use &[] for effs because we don't allow effect patterns in or patterns, for now
            let x = elab_pat(in_eff, x, ty, &[], vspan, reason.clone(), body_ret_ty, mcxt)?;
            if mcxt.size != size_before {
                todo!("error: for now we don't support capturing inside or-patterns")
            }
            let y = elab_pat(in_eff, y, ty, &[], vspan, reason, body_ret_ty, mcxt)?;
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
    body_ret_ty: Option<&VTy>,
    mcxt: &mut MCxt,
) -> Result<Pat, TypeError> {
    let span = Span(
        head.span().0,
        spine.back().map(|(_, x)| x.span()).unwrap_or(head.span()).1,
    );

    let (term, fty) = infer(false, head, mcxt)?;
    let (id, fty) = match term.inline_top(mcxt) {
        Term::Var(Var::Cons(id), _) => (id, fty),
        Term::Var(Var::Type(_, sid), _) => {
            let scope = mcxt.db.lookup_intern_scope(sid);
            let m = mcxt.db.intern_name(String::new());
            let mut found = None;
            let mut ty = fty;
            for &(n, v) in scope.iter() {
                if n == m {
                    ty = match mcxt.db.elaborate_def(v) {
                        Ok(info) => info.typ.into_owned(),
                        Err(_) => return Ok(Pat::Any),
                    };
                    found = Some(v);
                    break;
                }
            }
            if let Some(f) = found {
                (f, ty)
            } else {
                return Err(TypeError::InvalidPattern(span));
            }
        }
        _ => return Err(TypeError::InvalidPattern(span)),
    };

    let fty = UnifyRetType {
        fty,
        eff_ret: None,
        handle_effects: true,
        expected_ty,
        effs,
        vspan,
        span,
        reason: Some(&reason),
        mcxt,
    }
    .unify_ret_type()?;
    let mut eff_ret = None;

    let mut pspine = Vec::new();

    let before_size = mcxt.size;
    let arity = fty.arity(true);
    let f_arity = spine.iter().filter(|(i, _)| *i == Icit::Expl).count();
    let mut ty = fty.clone();

    // C :: (a : Type) -> (b : a) -> SomeType
    // case x of
    //   C _ b => ...
    // b :: ???
    // We actually need to make an additional local for each pi argument

    // TODO unify constructor effects with given ones
    while let Some((i, pat)) = spine.pop_front() {
        match ty {
            Val::Clos(Pi, Icit::Impl, cl, mut effs) if i == Icit::Expl => {
                // Add an implicit argument to the pattern, and keep the explicit one on the stack
                spine.push_front((i, pat));
                mcxt.define(cl.name, NameInfo::Local(cl.ty.clone()));
                pspine.push((
                    Some((cl.name, cl.ty.clone().quote(mcxt.size.dec(), mcxt))),
                    Pat::Any,
                ));
                ty = cl.vquote(mcxt.size.dec(), mcxt);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
            }
            Val::Clos(Pi, i2, cl, mut effs) if i == i2 => {
                // We need a shadow variable in case the pattern doesn't capture it
                let before_size = mcxt.size;
                mcxt.define(cl.name, NameInfo::Local(cl.ty.clone()));
                let v = Some((cl.name, cl.ty.clone().quote(before_size, mcxt)));

                let pat = elab_pat(
                    in_eff,
                    pat,
                    &cl.ty,
                    &[],
                    vspan,
                    reason.clone(),
                    body_ret_ty,
                    mcxt,
                )?;
                pspine.push((v, pat));
                ty = cl.vquote(before_size, mcxt);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
            }
            Val::Fun(from, to, mut effs) if i == Icit::Expl => {
                // No shadow variable needed, since it's not a pi
                let pat = elab_pat(
                    in_eff,
                    pat,
                    &from,
                    &[],
                    vspan,
                    reason.clone(),
                    body_ret_ty,
                    mcxt,
                )?;
                pspine.push((None, pat));
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
    }

    // Apply any remaining implicits
    loop {
        match ty {
            Val::Clos(Pi, Icit::Impl, cl, mut effs) => {
                mcxt.define(cl.name, NameInfo::Local(cl.ty.clone()));
                pspine.push((
                    Some((cl.name, cl.ty.clone().quote(mcxt.size.dec(), mcxt))),
                    Pat::Any,
                ));
                ty = cl.vquote(mcxt.size.dec(), mcxt);
                if !effs.is_empty() {
                    assert_eq!(effs.len(), 1);
                    eff_ret = Some(ty);
                    ty = effs.pop().unwrap();
                    break;
                }
            }
            ty2 => {
                // Put it back
                ty = ty2;
                break;
            }
        }
    }

    match &ty {
        Val::Fun(_, _, _) | Val::Clos(Pi, _, _, _) if eff_ret.is_none() => {
            return Err(TypeError::WrongArity(head.copy_span(fty), arity, f_arity))
        }
        _ => (),
    }

    let ty = UnifyRetType {
        fty: ty,
        eff_ret,
        handle_effects: true,
        expected_ty,
        effs,
        vspan,
        span,
        reason: Some(&reason),
        mcxt,
    }
    .unify_ret_type()?;
    Ok(Pat::Cons(id, Box::new(ty.quote(before_size, mcxt)), pspine))
}

struct UnifyRetType<'a, 'b> {
    fty: VTy,
    eff_ret: Option<Val>,
    handle_effects: bool,
    expected_ty: &'a VTy,
    effs: &'a [VTy],
    vspan: Span,
    span: Span,
    reason: Option<&'a ReasonExpected>,
    mcxt: &'a mut MCxt<'b>,
}
impl<'a, 'b> UnifyRetType<'a, 'b> {
    fn no_effects(fty: VTy, expected_ty: &'a VTy, mcxt: &'a mut MCxt<'b>) -> Self {
        UnifyRetType {
            fty,
            expected_ty,
            eff_ret: None,
            handle_effects: false,
            effs: &[],
            vspan: Span::empty(),
            span: Span::empty(),
            reason: None,
            mcxt,
        }
    }

    fn unify_ret_type(self) -> Result<VTy, TypeError> {
        let UnifyRetType {
            fty,
            mut eff_ret,
            handle_effects,
            expected_ty,
            effs,
            vspan,
            span,
            reason,
            mcxt,
        } = self;
        let fallback = ReasonExpected::UsedAsType;
        let reason = reason.unwrap_or(&fallback);
        let before_size = mcxt.size;

        let mut rty = fty.clone();
        loop {
            match rty {
                Val::Clos(Pi, _, cl, mut effs) => {
                    mcxt.define(
                        mcxt.db.intern_name("_".into()),
                        NameInfo::Local(cl.ty.clone()),
                    );
                    rty = cl.vquote(mcxt.size.dec(), mcxt);
                    if !effs.is_empty() {
                        assert_eq!(effs.len(), 1);
                        if handle_effects {
                            eff_ret = Some(rty);
                        }
                        rty = effs.pop().unwrap();
                        break;
                    }
                }
                Val::Fun(_, to, mut effs) => {
                    rty = *to;
                    if !effs.is_empty() {
                        assert_eq!(effs.len(), 1);
                        if handle_effects {
                            eff_ret = Some(rty);
                        }
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
                    crate::elaborate::local_unify(rty.clone(), e.clone(), mcxt.size, span, mcxt)
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
            match crate::elaborate::local_unify(
                eff_ret.clone(),
                expected_ty.clone(),
                mcxt.size,
                span,
                mcxt,
            ) {
                Ok(true) => (),
                Ok(false) => {
                    return Err(TypeError::InvalidPatternBecause(Box::new(
                        TypeError::Unify(
                            Spanned::new(eff_ret.inline_metas(mcxt.size, mcxt), span),
                            expected_ty.clone().inline_metas(mcxt.size, mcxt),
                            reason.clone(),
                        ),
                    )))
                }
                Err(e) => return Err(TypeError::InvalidPatternBecause(Box::new(e))),
            }
        } else {
            // Unify with the expected type, for GADTs and constructors of different datatypes
            match crate::elaborate::local_unify(
                rty.clone(),
                expected_ty.clone(),
                mcxt.size,
                span,
                mcxt,
            ) {
                Ok(true) => (),
                Ok(false) => {
                    return Err(TypeError::InvalidPatternBecause(Box::new(
                        TypeError::Unify(
                            Spanned::new(rty.clone().inline_metas(mcxt.size, mcxt), span),
                            expected_ty.clone().inline_metas(mcxt.size, mcxt),
                            reason.clone(),
                        ),
                    )))
                }
                Err(e) => return Err(TypeError::InvalidPatternBecause(Box::new(e))),
            }
        }

        let fty = fty
            .quote(before_size, mcxt)
            .evaluate(&Env::new(before_size), mcxt);

        while mcxt.size != before_size {
            mcxt.undef();
        }
        Ok(fty)
    }
}
