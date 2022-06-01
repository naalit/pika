use std::sync::RwLock;

use super::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Meta(u32);

pub enum SpecialBound {
    IntType { must_be_signed: bool, must_fit: u64 },
}

pub struct MetaBounds {
    ty: Val,
    special: Option<SpecialBound>,
}
impl MetaBounds {
    pub fn new(ty: Val) -> Self {
        MetaBounds { ty, special: None }
    }
    pub fn int_positive(val: u64) -> Self {
        MetaBounds {
            ty: Val::Type,
            special: Some(SpecialBound::IntType {
                must_be_signed: false,
                must_fit: val,
            }),
        }
    }
    pub fn int_negative(val: i64) -> Self {
        MetaBounds {
            ty: Val::Type,
            special: Some(SpecialBound::IntType {
                must_be_signed: true,
                // e.g.: -255 is guaranteed to fit if 255 can fit, and since it's signed that means I16+
                must_fit: (-val) as u64,
            }),
        }
    }
}

pub enum MetaEntry {
    Solved {
        solution: Expr,
        occurs_cache: RwLock<Option<Meta>>,
    },
    Unsolved {
        bounds: MetaBounds,
        scope: Size,
        introduced_span: RelSpan,
    },
}

pub enum MetaSolveError {
    Occurs(Meta),
    Scope(Name),
    SpineNonVariable(Val),
    SpineNonApp(Elim<Val>),
    SpineTooLong,
    SpineDuplicate(Name),
}

enum SolutionCheckMode {
    Occurs(Meta),
    Full(PartialRename),
}
impl SolutionCheckMode {
    fn occurs_meta(&self) -> Meta {
        match self {
            SolutionCheckMode::Occurs(m) => *m,
            SolutionCheckMode::Full(m) => m.meta,
        }
    }

    fn should_rename(&self) -> bool {
        match self {
            SolutionCheckMode::Occurs(_) => false,
            SolutionCheckMode::Full(_) => true,
        }
    }

    fn renamed(&self, l: Lvl) -> Option<Lvl> {
        match self {
            SolutionCheckMode::Occurs(_) => Some(l),
            SolutionCheckMode::Full(r) => r.vars.get(&l).copied(),
        }
    }
}

struct PartialRename {
    meta: Meta,
    vars: HashMap<Lvl, Lvl>,
}
impl PartialRename {
    fn add_arg(&mut self, arg: Val, inner_size: &mut Size) -> Result<Pat, MetaSolveError> {
        match arg {
            Val::Neutral(n)
                if matches!(n.head(), Head::Var(Var::Local(_, _))) && n.spine().is_empty() =>
            {
                let (n, l) = match n.head() {
                    Head::Var(Var::Local(n, l)) => (n, l),
                    _ => unreachable!(),
                };
                self.vars.insert(l, inner_size.next_lvl());
                *inner_size = inner_size.inc();

                Ok(Pat::Var(n))
            }
            // only right-associative pairs are allowed
            // TODO when box patterns are stabilized switch to that instead of nested matches!()
            Val::Pair(a, b)
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
                self.vars.insert(l, inner_size.next_lvl());
                *inner_size = inner_size.inc();

                let rhs = self.add_arg(*b, inner_size)?;
                Ok(todo!("Pat::Pair(Box::new(Pat::Var(n)), rhs)"))
            }
            // TODO handle Val::Error without creating more errors?
            v => Err(MetaSolveError::SpineNonVariable(v)),
        }
    }
}

pub struct MetaCxt {
    metas: Vec<MetaEntry>,
}
impl MetaCxt {
    pub fn new_meta(&mut self, scope: Size, bounds: MetaBounds, introduced_span: RelSpan) -> Meta {
        let m = Meta(self.metas.len() as u32);
        self.metas.push(MetaEntry::Unsolved {
            bounds,
            scope,
            introduced_span,
        });
        m
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

    pub fn lookup(&self, meta: Meta) -> Option<Expr> {
        self.metas.get(meta.0 as usize).and_then(|x| match x {
            MetaEntry::Solved { solution, .. } => Some(solution.clone()),
            MetaEntry::Unsolved { .. } => None,
        })
    }

    pub fn solve(
        &mut self,
        start_size: Size,
        meta: Meta,
        mut spine: Vec<Elim<Val>>,
        solution: Val,
    ) -> Result<(), MetaSolveError> {
        // smalltt does eta-contraction here, but I don't think that's necessary, especially without explicit meta spines in most cases

        // TODO check against `bounds`, which should be done before quoting

        let (scope, bounds, intro_span) = self
            .metas
            .get(meta.0 as usize)
            .and_then(|x| match x {
                MetaEntry::Solved { .. } => None,
                MetaEntry::Unsolved {
                    scope,
                    bounds,
                    introduced_span,
                } => Some((scope, bounds, introduced_span)),
            })
            .unwrap();

        let mut rename = PartialRename {
            meta,
            vars: HashMap::new(),
        };
        // Map all locals in the meta's scope to themselves (they must still be bound)
        for i in Size::zero().until(*scope) {
            rename.vars.insert(i.next_lvl(), i.next_lvl());
        }
        // Inspect the spine to allow user-defined variable dependencies
        let mut inner_size = start_size;
        if spine.len() > 1 {
            return Err(MetaSolveError::SpineTooLong);
        }
        let params = spine
            .pop()
            .map(|elim| match elim {
                Elim::App(args) if args.implicit.is_empty() && args.explicit.is_some() => {
                    let pat = rename.add_arg(*args.explicit.unwrap(), &mut inner_size)?;
                    Ok(Params {
                        implicit: Vec::new(),
                        explicit: Some(Box::new(Par {
                            pat,
                            // TODO is this type ever used? can we actually find the type of this?
                            ty: Val::Error,
                        })),
                    })
                }
                i => Err(MetaSolveError::SpineNonApp(i)),
            })
            .transpose()?;
        let inner_size_scope = start_size
            .until(inner_size)
            .fold(*scope, |acc, _| acc.inc());

        let mut solution = solution.quote(inner_size);
        solution.check_solution(
            self,
            &SolutionCheckMode::Full(rename),
            inner_size,
            inner_size_scope,
        )?;

        if let Some(params) = params {
            let (params, i2) = params.quote(*scope);
            assert_eq!(i2, inner_size_scope);
            solution = Expr::Fun {
                class: Lam,
                params,
                body: Box::new(solution),
            }
        }

        self.metas[meta.0 as usize] = MetaEntry::Solved {
            solution,
            occurs_cache: RwLock::new(None),
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
            Elim::App(args) => {
                for i in args.implicit.iter_mut().chain(args.explicit.as_deref_mut()) {
                    i.check_solution(cxt, mode, s_from, s_to)?;
                }
            }
            Elim::Member(_) => todo!(),
            Elim::Case(_) => todo!(),
        }
        Ok(())
    }
}

impl Params<Expr> {
    fn check_solution(
        &mut self,
        cxt: &MetaCxt,
        mode: &SolutionCheckMode,
        mut s_from: Size,
        mut s_to: Size,
    ) -> Result<(Size, Size), MetaSolveError> {
        for i in self.implicit.iter_mut().chain(self.explicit.as_deref_mut()) {
            i.ty.check_solution(cxt, mode, s_from, s_to)?;
            s_from = i.pat.add_to_size(s_from);
            s_to = i.pat.add_to_size(s_to);
        }
        Ok((s_from, s_to))
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
            Expr::Head(h) => match h {
                Head::Var(Var::Local(n, i)) if mode.should_rename() => {
                    match mode.renamed(i.lvl(s_from)) {
                        Some(l) => *i = l.idx(s_to),
                        None => return Err(MetaSolveError::Scope(*n)),
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
                // TODO we don't currently do any unfolding during solution checking
                // this is sound, but we miss possible solutions (smalltt's example is `?0 = const true y` where y is not in the meta scope)
                _ => (),
            },
            Expr::Elim(a, b) => {
                a.check_solution(cxt, mode, s_from, s_to)?;
                b.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Pair(a, b) => {
                a.check_solution(cxt, mode, s_from, s_to)?;
                b.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Fun {
                class: _,
                params,
                body,
            } => {
                let (s_from, s_to) = params.check_solution(cxt, mode, s_from, s_to)?;
                body.check_solution(cxt, mode, s_from, s_to)?;
            }
            Expr::Lit(_) | Expr::Type | Expr::Error => (),
        }
        Ok(())
    }
}
