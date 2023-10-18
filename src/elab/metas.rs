use std::sync::{Arc, RwLock};

use super::{unify::UnifyError, *};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct Meta(u32);
impl std::fmt::Display for Meta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

#[derive(Clone, Debug)]
pub enum SpecialBound {
    IntType { must_fit: i128 },
}

#[derive(Clone, Debug)]
pub struct MetaBounds {
    ty: Val,
    special: Option<SpecialBound>,
    is_impl: bool,
    stored: Vec<(Size, Vec<Elim<Val>>, Val)>,
}
impl MetaBounds {
    pub fn new(ty: Val) -> Self {
        MetaBounds {
            ty,
            special: None,
            is_impl: false,
            stored: Vec::new(),
        }
    }
    pub fn int_type(signed: bool, val: u64) -> Self {
        MetaBounds {
            ty: Val::Type,
            special: Some(SpecialBound::IntType {
                must_fit: if signed {
                    val as i64 as i128
                } else {
                    val as i128
                },
            }),
            is_impl: false,
            stored: Vec::new(),
        }
    }

    pub fn with_impl(self, is_impl: bool) -> Self {
        MetaBounds { is_impl, ..self }
    }

    pub fn check(
        self,
        val: &Val,
        spine_len: usize,
        size: Size,
        mcxt: &mut MetaCxt,
    ) -> Result<(), MetaSolveError> {
        // TODO check type

        for (msize, spine, other_val) in self.stored {
            let size = size.max(msize);
            let val = spine
                .into_iter()
                .skip(spine_len)
                .fold(val.clone(), |head, elim| {
                    head.app(elim, &mut Env::new(size))
                });
            match mcxt.unify(
                val.clone(),
                other_val,
                size,
                Env::new(size),
                CheckReason::UsedAsType,
            ) {
                Ok(()) => (),
                Err(u) => {
                    return Err(MetaSolveError::Other(
                        Doc::start("Conflict solving meta: ")
                            .chain(u.to_error(RelSpan::empty(), mcxt.db).message),
                    ));
                }
            }
        }

        match self.special {
            Some(SpecialBound::IntType { must_fit }) => {
                let mut val = val.clone();
                val.inline_head(&mut Env::new(size), mcxt);
                match val {
                    Val::Neutral(ref n)
                        if matches!(
                            n.head(),
                            Head::Var(Var::Builtin(Builtin::IntType(_))) | Head::Var(Var::Meta(_))
                        ) =>
                    {
                        match n.head() {
                            Head::Var(Var::Builtin(Builtin::IntType(t))) => {
                                if must_fit >= t.min() && must_fit <= t.max() {
                                    Ok(())
                                } else {
                                    Err(MetaSolveError::BoundsWrongIntSize(t))
                                }
                            }
                            Head::Var(Var::Meta(m)) => {
                                match &mcxt.metas[m.0 as usize] {
                                    MetaEntry::Unsolved { bounds, .. } => {
                                        // TODO actually merge bounds
                                        if matches!(
                                            &bounds.special,
                                            Some(SpecialBound::IntType { .. })
                                        ) {
                                            return Ok(());
                                        }
                                    }
                                    MetaEntry::Solved { .. } => (),
                                }
                                Err(MetaSolveError::BoundsNotInt(val.quote(size, None)))
                            }
                            _ => unreachable!(),
                        }
                    }
                    Val::Error => Ok(()),
                    val => Err(MetaSolveError::BoundsNotInt(val.quote(size, None))),
                }
            }
            None => Ok(()),
        }
    }
}

#[derive(Clone, Debug)]
pub enum MetaSource {
    Hole,
    TypeOf(Name),
    ArgOf(Doc, Option<Name>),
    Other(Doc),
}
impl MetaSource {
    fn pretty(&self, db: &(impl Elaborator + ?Sized)) -> Doc {
        match self {
            MetaSource::Hole => Doc::start("hole"),
            MetaSource::TypeOf(n) => Doc::start("type of '").chain(n.pretty(db)).add("'", ()),
            MetaSource::ArgOf(d, Some(n)) if *n != db.name("_".into()) => {
                Doc::start("implicit argument '")
                    .chain(n.pretty(db))
                    .add("' to function '", ())
                    .chain(d.clone())
                    .add("'", ())
            }
            MetaSource::ArgOf(d, _) => Doc::start("implicit argument to function '")
                .chain(d.clone())
                .add("'", ()),
            MetaSource::Other(d) => d.clone(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum MetaEntry {
    Solved {
        /// A lambda term with no free variables
        solution: Expr,
        occurs_cache: Arc<RwLock<Option<Meta>>>,
    },
    Unsolved {
        bounds: MetaBounds,
        size: Size,
        introduced_span: RelSpan,
        source: MetaSource,
    },
}

pub enum MetaSolveError {
    Occurs(Meta),
    Scope(Name),
    ScopeMeta(Meta),
    SpineNonVariable(Expr),
    SpineNonApp(Elim<Expr>),
    SpineDuplicate(Name),
    BoundsNotInt(Expr),
    BoundsWrongIntSize(IntType),
    Other(Doc),
}
impl MetaSolveError {
    pub fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        match self {
            MetaSolveError::Occurs(m) => Doc::start("Solved meta ")
                .add(m, Doc::COLOR1)
                .add(" occurs in solution", ()),
            MetaSolveError::ScopeMeta(m) => Doc::start("Meta ").add(m, Doc::COLOR1).add(
                ", which is outside of the scope of the meta, occurs in solution",
                (),
            ),
            MetaSolveError::Scope(n) => Doc::start("Variable ")
                .add(db.lookup_name(*n), Doc::COLOR1)
                .add(
                    ", which is outside of the scope of the meta, occurs in solution",
                    (),
                ),
            MetaSolveError::SpineNonVariable(e) => {
                Doc::start("Meta is applied to something other than a local variable: '")
                    .chain(e.pretty(db))
                    .add("'", ())
            }
            MetaSolveError::SpineNonApp(e) => Doc::start("Meta is used by illegal eliminator ")
                .add(
                    match e {
                        Elim::App(Impl, _) => "implicit application",
                        Elim::App(_, _) => unreachable!(),
                        Elim::Member(_, _, _) => "member access",
                        Elim::Case(_, _) => "case-of",
                    },
                    (),
                ),
            MetaSolveError::SpineDuplicate(n) => Doc::start("Meta is applied to variable ")
                .add(db.lookup_name(*n), Doc::COLOR1)
                .add(" more than once", ()),
            MetaSolveError::BoundsNotInt(t) => Doc::start("Integer literal can't have type '")
                .chain(t.pretty(db))
                .add("'", ()),
            MetaSolveError::BoundsWrongIntSize(t) => {
                Doc::start("Integer literal doesn't fit in type '")
                    .debug(t)
                    .add("'", ())
            }
            MetaSolveError::Other(doc) => doc.clone(),
        }
    }
}

enum SolutionCheckMode {
    Occurs(Meta),
    Full(PartialRename, Size),
}
impl SolutionCheckMode {
    fn occurs_meta(&self) -> Meta {
        match self {
            SolutionCheckMode::Occurs(m) => *m,
            SolutionCheckMode::Full(m, _) => m.meta,
        }
    }

    fn should_rename(&self) -> bool {
        match self {
            SolutionCheckMode::Occurs(_) => false,
            SolutionCheckMode::Full(_, _) => true,
        }
    }

    fn renamed(&self, i: Idx, s_from: Size, s_to: Size) -> Option<Idx> {
        let l = i.lvl(s_from);
        match self {
            SolutionCheckMode::Occurs(_) => Some(l.idx(s_to)),
            SolutionCheckMode::Full(r, s) => {
                if l.in_scope(*s) {
                    r.vars.get(&l).copied().map(|l| l.idx(s_to))
                } else {
                    // This var was introduced by an abstraction within the solution, it's fine
                    // We need to preserve the *index*, not the *level*, from the solution
                    Some(i)
                }
            }
        }
    }
}

struct PartialRename {
    meta: Meta,
    vars: HashMap<Lvl, Lvl>,
}
impl PartialRename {
    fn add_arg(
        &mut self,
        arg: Val,
        inner_size: Size,
        mcxt: &MetaCxt,
    ) -> Result<Vec<Name>, MetaSolveError> {
        match arg {
            Val::Neutral(n)
                if matches!(n.head(), Head::Var(Var::Local(_, _))) && n.spine().is_empty() =>
            {
                let (n, l) = match n.head() {
                    Head::Var(Var::Local(n, l)) => (n, l),
                    _ => unreachable!(),
                };
                // Non-linear meta spines arise because of the way we do local unification in patterns
                // so unless that changes anytime soon we'll just have suboptimal meta solutions
                // they're still "correct", just not 100% general, and we pick the first occurence of each var
                // (old smalltt used to do this so it can't be that bad)
                self.vars.entry(l).or_insert(inner_size.next_lvl());

                // if self.vars.insert(l, inner_size.next_lvl()).is_some() {
                //     return Err(MetaSolveError::SpineDuplicate(n.0));
                // }

                Ok(vec![n.0])
            }
            // only right-associative pairs are allowed
            // TODO when box patterns are stabilized switch to that instead of nested matches!()
            Val::Pair(a, b, _)
                if matches!(
                        &*a,
                        Val::Neutral(n)
                            if matches!(n.head(), Head::Var(Var::Local(_, _))) && n.spine().is_empty()
                ) =>
            {
                let h = match &*a {
                    Val::Neutral(n) => n.head(),
                    _ => unreachable!(),
                };
                let (n, l) = match h {
                    Head::Var(Var::Local(n, l)) => (n, l),
                    _ => unreachable!(),
                };
                self.vars.entry(l).or_insert(inner_size.next_lvl());
                // if self.vars.insert(l, inner_size.next_lvl()).is_some() {
                //     return Err(MetaSolveError::SpineDuplicate(n.0));
                // }

                let mut rhs = self.add_arg(*b, inner_size.inc(), mcxt)?;
                rhs.insert(0, n.0);
                Ok(rhs)
            }
            // TODO handle Val::Error without creating more errors?
            // Problem: when we solve locals, we get non-variables even if the meta spine used to be legal
            // This doesn't happen in smalltt because it doesn't solve locals
            // Ideally we track solved locals in some way so that we can skip them here
            // and then we can put back the non-linear spine errors as well.
            // However, ignoring everything but locals does work in practice
            _ => Ok(vec![mcxt.db.name("_".into())]),
            // v => Err(MetaSolveError::SpineNonVariable(
            //     v.quote(inner_size, Some(mcxt)),
            // )),
        }
    }
}

#[derive(Clone)]
pub struct MetaCheckpoint(usize);

#[derive(Clone)]
pub struct MetaCxt<'a> {
    pub db: &'a dyn Elaborator,
    metas: Vec<MetaEntry>,
}
impl MetaCxt<'_> {
    pub fn new(db: &dyn Elaborator) -> MetaCxt {
        MetaCxt {
            db,
            metas: Vec::new(),
        }
    }

    pub fn checkpoint(&self) -> MetaCheckpoint {
        MetaCheckpoint(self.metas.len())
    }

    pub fn reset_to(&mut self, MetaCheckpoint(len): MetaCheckpoint) {
        self.metas.truncate(len);
    }

    /// Creates a new meta which can't use any free variables; mostly for e.g. int types
    pub fn unscoped_meta(
        &mut self,
        bounds: MetaBounds,
        introduced_span: RelSpan,
        source: MetaSource,
    ) -> Meta {
        let m = Meta(self.metas.len() as u32);
        self.metas.push(MetaEntry::Unsolved {
            bounds,
            size: Size::zero(),
            introduced_span,
            source,
        });
        m
    }

    pub fn new_meta(
        &mut self,
        scope: Vec<(Name, Lvl)>,
        size: Size,
        bounds: MetaBounds,
        introduced_span: RelSpan,
        source: MetaSource,
    ) -> Expr {
        let m = Meta(self.metas.len() as u32);
        self.metas.push(MetaEntry::Unsolved {
            bounds,
            size,
            introduced_span,
            source,
        });
        let size = Size::zero() + scope.len();
        // The order of arguments shouldn't matter as long as they're all there
        let arg = scope.into_iter().fold(None, |rest, (n, l)| {
            let x = Expr::var(Var::Local((n, RelSpan::empty()), l.idx(size)));
            match rest {
                // TODO do we ever need these types?
                Some(rest) => Some(Expr::Pair(
                    Box::new(x),
                    Box::new(rest),
                    Box::new(Expr::Error),
                )),
                None => Some(x),
            }
        });
        match arg {
            None => Expr::var(Var::Meta(m)),
            Some(arg) => Expr::Elim(
                Box::new(Expr::var(Var::Meta(m))),
                Box::new(Elim::App(Expl, arg)),
            ),
        }
    }

    pub fn is_solved(&self, meta: Meta) -> bool {
        self.metas
            .get(meta.0 as usize)
            .map(|x| match x {
                MetaEntry::Solved { .. } => true,
                MetaEntry::Unsolved { .. } => false,
            })
            .unwrap_or(true)
    }

    pub fn meta_ty(&self, meta: Meta) -> Option<Val> {
        self.metas.get(meta.0 as usize).and_then(|x| match x {
            // TODO maybe store type of solved metas?
            MetaEntry::Solved { .. } => None,
            MetaEntry::Unsolved { bounds, .. } => Some(bounds.ty.clone()),
        })
    }

    pub fn lookup(&self, meta: Meta) -> Option<Expr> {
        self.metas.get(meta.0 as usize).and_then(|x| match x {
            MetaEntry::Solved { solution, .. } => Some(solution.clone()),
            MetaEntry::Unsolved { .. } => None,
        })
    }

    pub fn introduced_span(&self, meta: Meta) -> RelSpan {
        self.metas
            .get(meta.0 as usize)
            .and_then(|x| match x {
                MetaEntry::Solved { .. } => None,
                MetaEntry::Unsolved {
                    introduced_span, ..
                } => Some(*introduced_span),
            })
            .unwrap()
    }

    pub fn solve(
        &mut self,
        start_size: Size,
        meta: Meta,
        spine: Vec<Elim<Val>>,
        solution: Val,
        allow_impl: bool,
    ) -> Result<(), MetaSolveError> {
        // TODO smalltt does eta-contraction here

        let (bounds, _intro_span) = self
            .metas
            .get_mut(meta.0 as usize)
            .and_then(|x| match x {
                MetaEntry::Solved { .. } => None,
                MetaEntry::Unsolved {
                    bounds,
                    size: _,
                    introduced_span,
                    source: _,
                } => Some((bounds, introduced_span)),
            })
            .unwrap();
        // If spine.len() > 1, we don't know for sure this is the correct solution
        // so postpone this solution to see if we find a better one later (and check that they match)
        if !allow_impl && (bounds.is_impl || spine.len() > 1) {
            bounds.stored.push((start_size, spine, solution));
            return Ok(());
        }
        // TODO not clone here
        bounds
            .clone()
            .check(&solution, spine.len(), start_size, self)?;

        let mut rename = PartialRename {
            meta,
            vars: HashMap::new(),
        };
        let params: Vec<(Vec<_>, Icit)> = {
            let mut size_to = Size::zero();
            spine
                .into_iter()
                .map(|elim| match elim {
                    Elim::App(icit, arg) => {
                        let names = rename.add_arg(arg, size_to, self)?;
                        size_to += names.len();
                        Ok((
                            names
                                .into_iter()
                                // TODO is this type ever used? can we actually find the type of this?
                                .map(|name| Par::new((name, RelSpan::empty()), Expr::Error, false))
                                .collect(),
                            icit,
                        ))
                    }
                    i => Err(MetaSolveError::SpineNonApp(i.quote(start_size, Some(self)))),
                })
                .collect::<Result<_, _>>()?
        };
        let inner_size_from = start_size + params.iter().map(|(x, _)| x.len()).sum();
        let inner_size_to = Size::zero() + params.iter().map(|(x, _)| x.len()).sum();

        // Try to avoid inlining metas in the solution to keep it small
        let mut solution = solution.quote(inner_size_from, None);
        let solution2 = solution.clone();
        let mode = SolutionCheckMode::Full(rename, inner_size_from);
        match solution.check_solution(self, &mode, inner_size_from, inner_size_to) {
            Ok(()) => (),
            Err(_) => {
                // Inline metas if we have to
                solution = solution2.eval_quote(
                    &mut Env::new(inner_size_from),
                    inner_size_from,
                    Some(self),
                );
                solution.check_solution(self, &mode, inner_size_from, inner_size_to)?;
            }
        };

        for (params, icit) in params.into_iter().rev() {
            solution = Expr::Fun(EClos {
                class: Lam(icit, Cap::Imm),
                params,
                body: Box::new(solution),
            })
        }

        self.metas[meta.0 as usize] = MetaEntry::Solved {
            solution,
            occurs_cache: Arc::new(RwLock::new(None)),
        };

        Ok(())
    }

    pub fn needed_impls(&self, next_size: Size) -> Vec<(Meta, Size, RelSpan)> {
        let mut metas = Vec::new();
        for i in 0..self.metas.len() {
            match self.metas[i].clone() {
                MetaEntry::Unsolved {
                    bounds,
                    size,
                    introduced_span,
                    source: _,
                } if bounds.is_impl && size >= next_size => {
                    metas.push((Meta(i as u32), size, introduced_span));
                }
                _ => (),
            }
        }
        metas
    }

    pub fn mark_meta_error(&mut self, meta: Meta) {
        // Make sure we don't emit duplicate errors
        self.metas[meta.0 as usize] = MetaEntry::Solved {
            solution: Expr::Error,
            occurs_cache: Default::default(),
        };
    }

    pub fn error_unsolved(&mut self) -> Vec<Error> {
        let mut errors = Vec::new();
        for i in 0..self.metas.len() {
            match &mut self.metas[i] {
                MetaEntry::Solved { .. } => (),
                MetaEntry::Unsolved {
                    bounds,
                    size,
                    introduced_span,
                    source,
                } => {
                    let intro_span = *introduced_span;
                    match bounds.stored.pop() {
                        None => errors.push(
                            TypeError::Other(
                                // TODO store a Doc or enum for the reason the meta was introduced
                                Doc::start("Could not find solution for ")
                                    .chain(source.pretty(self.db))
                                    .add(", of type '", ())
                                    .chain(
                                        bounds.ty.clone().quote(*size, Some(self)).pretty(self.db),
                                    )
                                    .add("', introduced here", ()),
                            )
                            .to_error(
                                Severity::Error,
                                intro_span,
                                self.db,
                            ),
                        ),
                        Some((msize, spine, solution)) => {
                            if let Err(e) = self.solve(msize, Meta(i as u32), spine, solution, true)
                            {
                                errors.push(
                                    UnifyError::from_meta_solve(e, intro_span)
                                        .to_error(intro_span, self.db),
                                );
                            }
                        }
                    }
                }
            }
        }
        errors
    }
}

impl Elim<Expr> {
    fn check_solution(
        &mut self,
        cxt: &MetaCxt,
        mode: &SolutionCheckMode,
        s_from: Size,
        s_to: Size,
    ) -> Result<(), MetaSolveError> {
        match self {
            Elim::App(_, x) => {
                x.check_solution(cxt, mode, s_from, s_to)?;
            }
            Elim::Member(_, _, _) => (),
            Elim::Case(_, _) => todo!(),
        }
        Ok(())
    }
}

impl Expr {
    fn check_solution(
        &mut self,
        cxt: &MetaCxt,
        mode: &SolutionCheckMode,
        s_from: Size,
        s_to: Size,
    ) -> Result<(), MetaSolveError> {
        match self {
            Expr::Spanned(_, x) => x.check_solution(cxt, mode, s_from, s_to)?,
            Expr::Head(h) => match h {
                Head::Var(Var::Local(n, i)) if mode.should_rename() => {
                    match mode.renamed(*i, s_from, s_to) {
                        Some(l) => *i = l,
                        None => return Err(MetaSolveError::Scope(n.0)),
                    }
                }
                Head::Var(Var::Meta(m)) if *m == mode.occurs_meta() => {
                    return Err(MetaSolveError::Occurs(*m))
                }
                Head::Var(Var::Meta(m)) => match &cxt.metas.get(m.0 as usize) {
                    Some(MetaEntry::Solved {
                        solution,
                        occurs_cache,
                        ..
                    }) => {
                        if *occurs_cache.read().unwrap() != Some(mode.occurs_meta()) {
                            // TODO is the only option to avoid cloning here to make a separate check_solution() function for occurs-only?
                            solution.clone().check_solution(
                                cxt,
                                &SolutionCheckMode::Occurs(mode.occurs_meta()),
                                Size::zero(),
                                Size::zero(),
                            )?;
                            *occurs_cache.write().unwrap() = Some(mode.occurs_meta());
                        }
                    }
                    Some(MetaEntry::Unsolved { .. }) => (),
                    // TODO this case probably shouldn't happen, not sure why it sometimes triggers right now
                    None => return Err(MetaSolveError::ScopeMeta(*m)),
                },
                // TODO unfold here instead of in solve()
                _ => (),
            },
            Expr::Cap(_, x) => x.check_solution(cxt, mode, s_from, s_to)?,
            Expr::Assign(place, expr) => {
                place.check_solution(cxt, mode, s_from, s_to)?;
                expr.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Elim(a, b) => {
                a.check_solution(cxt, mode, s_from, s_to)?;
                b.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Pair(a, b, t) => {
                a.check_solution(cxt, mode, s_from, s_to)?;
                b.check_solution(cxt, mode, s_from, s_to)?;
                t.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Struct(_, fields, ty) => {
                for i in fields {
                    i.check_solution(cxt, mode, s_from, s_to)?;
                }
                ty.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Fun(EClos {
                class: _,
                params,
                body,
            }) => {
                let (mut s_from, mut s_to) = (s_from, s_to);
                for i in params.iter_mut() {
                    i.ty.check_solution(cxt, mode, s_from, s_to)?;
                    s_from += 1;
                    s_to += 1;
                }
                body.check_solution(cxt, mode, s_from + params.len(), s_to + params.len())?;
            }
            Expr::Lit(_) | Expr::Type | Expr::Error => (),
        }
        Ok(())
    }
}
