use std::sync::{Arc, RwLock};

use super::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Hash)]
pub struct Meta(u32);
impl std::fmt::Display for Meta {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

#[derive(Clone)]
pub enum SpecialBound {
    IntType { must_fit: i128 },
}

#[derive(Clone)]
pub struct MetaBounds {
    ty: Val,
    special: Option<SpecialBound>,
}
impl MetaBounds {
    pub fn new(ty: Val) -> Self {
        MetaBounds { ty, special: None }
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
        }
    }

    pub fn check(&self, val: &Val, size: Size, mcxt: &MetaCxt) -> Result<(), MetaSolveError> {
        // TODO check type
        match self.special {
            Some(SpecialBound::IntType { must_fit }) => {
                let mut val = val.clone();
                val.inline_head(&mut Env::new(size), mcxt);
                match val.no_deps() {
                    Val::Neutral(n)
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
                    _ => Err(MetaSolveError::BoundsNotInt(val.quote(size, None))),
                }
            }
            None => Ok(()),
        }
    }
}

#[derive(Clone)]
pub enum MetaEntry {
    Solved {
        /// A lambda term with no free variables
        solution: Expr,
        occurs_cache: Arc<RwLock<Option<Meta>>>,
    },
    Unsolved {
        bounds: MetaBounds,
        introduced_span: RelSpan,
    },
}

pub enum MetaSolveError {
    Occurs(Meta),
    Scope(Name),
    SpineNonVariable(Expr),
    SpineNonApp(Elim<Expr>),
    SpineDuplicate(Name),
    BoundsNotInt(Expr),
    BoundsWrongIntSize(IntType),
}
impl MetaSolveError {
    pub fn pretty<T: Elaborator + ?Sized>(&self, db: &T) -> Doc {
        match self {
            MetaSolveError::Occurs(m) => Doc::start("Solved meta ")
                .add(m, Doc::COLOR1)
                .add(" occurs in solution", ()),
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
                        Elim::Member(_) => "member access",
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
                if self.vars.insert(l, inner_size.next_lvl()).is_some() {
                    return Err(MetaSolveError::SpineDuplicate(n.0));
                }

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
                if self.vars.insert(l, inner_size.next_lvl()).is_some() {
                    return Err(MetaSolveError::SpineDuplicate(n.0));
                }

                let mut rhs = self.add_arg(*b, inner_size.inc(), mcxt)?;
                rhs.insert(0, n.0);
                Ok(rhs)
            }
            // TODO handle Val::Error without creating more errors?
            v => Err(MetaSolveError::SpineNonVariable(
                v.quote(inner_size, Some(mcxt)),
            )),
        }
    }
}

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

    /// Creates a new meta which can't use any free variables; mostly for e.g. int types
    pub fn unscoped_meta(&mut self, bounds: MetaBounds, introduced_span: RelSpan) -> Meta {
        let m = Meta(self.metas.len() as u32);
        self.metas.push(MetaEntry::Unsolved {
            bounds,
            introduced_span,
        });
        m
    }

    pub fn new_meta(
        &mut self,
        scope: Vec<(Name, Lvl)>,
        bounds: MetaBounds,
        introduced_span: RelSpan,
    ) -> Expr {
        let m = Meta(self.metas.len() as u32);
        self.metas.push(MetaEntry::Unsolved {
            bounds,
            introduced_span,
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
            .unwrap_or(false)
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
    ) -> Result<(), MetaSolveError> {
        // TODO smalltt does eta-contraction here

        let (bounds, _intro_span) = self
            .metas
            .get(meta.0 as usize)
            .and_then(|x| match x {
                MetaEntry::Solved { .. } => None,
                MetaEntry::Unsolved {
                    bounds,
                    introduced_span,
                } => Some((bounds, introduced_span)),
            })
            .unwrap();
        bounds.check(&solution, start_size, self)?;

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
                                .map(|name| Par {
                                    name: (name, RelSpan::empty()),
                                    // TODO is this type ever used? can we actually find the type of this?
                                    ty: Expr::Error,
                                })
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
        let mode = SolutionCheckMode::Full(rename, inner_size_to);
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
                class: Lam(icit),
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
            Elim::Member(_) => todo!(),
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
                Head::Var(Var::Meta(m)) => match &cxt.metas[m.0 as usize] {
                    MetaEntry::Solved {
                        solution,
                        occurs_cache,
                        ..
                    } => {
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
                    MetaEntry::Unsolved { .. } => (),
                },
                // TODO unfold here instead of in solve()
                _ => (),
            },
            Expr::Elim(a, b) => {
                a.check_solution(cxt, mode, s_from, s_to)?;
                b.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Pair(a, b, t) => {
                a.check_solution(cxt, mode, s_from, s_to)?;
                b.check_solution(cxt, mode, s_from, s_to)?;
                t.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Dep(v, t) => {
                for i in v {
                    i.check_solution(cxt, mode, s_from, s_to)?;
                }
                t.check_solution(cxt, mode, s_from, s_to)?;
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
