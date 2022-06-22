use super::*;

/// By default this implements the same scheme smalltt uses - we try without unfolding once, then give up and unfold everything.
/// However, all the logic is contained in this type and could be changed pretty easily.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum UnfoldState {
    /// Rigid in smalltt
    /// Something to try in the future is Maybe(n_tries)
    Maybe,
    /// Flex in smalltt
    Never,
    /// Full in smalltt
    Always,
}
impl Default for UnfoldState {
    fn default() -> Self {
        UnfoldState::Maybe
    }
}
impl UnfoldState {
    fn try_approx(self) -> bool {
        match self {
            UnfoldState::Maybe => true,
            UnfoldState::Never => true,
            UnfoldState::Always => false,
        }
    }

    /// If we're in this state and we fail approximate conversion checking, check whether we can switch to an unfolding mode and if so which one.
    /// Must not return the same mode, or an infinite loop would occur.
    fn approx_fail_mode(self) -> Option<UnfoldState> {
        match self {
            UnfoldState::Maybe => Some(UnfoldState::Always),
            UnfoldState::Never => None,
            UnfoldState::Always => unreachable!(),
        }
    }

    fn can_unfold(self) -> bool {
        match self {
            UnfoldState::Maybe => true,
            UnfoldState::Never => false,
            UnfoldState::Always => true,
        }
    }

    fn spine_mode(self) -> UnfoldState {
        match self {
            UnfoldState::Maybe => UnfoldState::Never,
            UnfoldState::Never => UnfoldState::Never,
            UnfoldState::Always => UnfoldState::Always,
        }
    }

    fn can_solve_metas(self) -> bool {
        match self {
            UnfoldState::Maybe => true,
            // TODO setting this to true enables approximate solutions; do we want that?
            UnfoldState::Never => false,
            UnfoldState::Always => true,
        }
    }
}

struct UnifyCxt<'a> {
    meta_cxt: &'a mut MetaCxt,
}

pub enum UnifyError {
    /// (Inferred, Expected)
    Conversion(Expr, Expr),
    MetaSolve(MetaSolveError),
}
impl UnifyError {
    pub fn to_error(&self, span: RelSpan, db: &dyn Elaborator) -> Error {
        let mut gen = ariadne::ColorGenerator::new();
        let ca = gen.next();
        let (msg, label, note) = match self {
            UnifyError::Conversion(a, b) => (
                Doc::start("Could not match types '")
                    .chain(a.pretty(db))
                    .add("' and '", ())
                    .chain(b.pretty(db))
                    .add("'", ()),
                Doc::start("Expected type '")
                    .chain(b.pretty(db))
                    .add("'", ()),
                None,
            ),
            UnifyError::MetaSolve(m) => (
                Doc::start("Error solving metavariable: ").chain(m.pretty(db)),
                Doc::start("Meta solution found here"),
                None,
            ),
        };
        Error {
            severity: Severity::Error,
            message: msg,
            primary: Label {
                span,
                message: label,
                color: Some(ca),
            },
            secondary: Vec::new(),
            note,
        }
    }
}

impl MetaCxt {
    /// When possible, (inferred, expected)
    pub fn unify(&mut self, a: Val, b: Val, size: Size) -> Result<(), UnifyError> {
        UnifyCxt { meta_cxt: self }.unify(a, b, size, UnfoldState::default())
    }
}

impl UnifyCxt<'_> {
    fn unify_spines(
        &mut self,
        a: &[Elim<Val>],
        b: &[Elim<Val>],
        size: Size,
        state: UnfoldState,
    ) -> Result<bool, UnifyError> {
        if a.len() != b.len() {
            return Ok(false);
        }
        for (a, b) in a.iter().zip(b) {
            match (a, b) {
                (Elim::App(i1, a), Elim::App(i2, b)) if i1 == i2 => {
                    self.unify(a.clone(), b.clone(), size, state)?;
                }
                (Elim::Member(_), Elim::Member(_)) => todo!(),
                (Elim::Case(_), Elim::Case(_)) => todo!(),

                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn unify(&mut self, a: Val, b: Val, size: Size, state: UnfoldState) -> Result<(), UnifyError> {
        match (a, b) {
            (Val::Type, Val::Type) => Ok(()),
            (Val::Error, _) | (_, Val::Error) => Ok(()),
            (Val::Fun(a), Val::Fun(b))
                if a.class == b.class && a.params.len() == b.params.len() =>
            {
                // First unify parameters
                self.unify(a.par_ty(), b.par_ty(), size, state)?;

                // Unify bodies
                let new_size = size + a.params.len().max(b.params.len());
                let a = a.open(size);
                let b = b.open(size);
                self.unify(a, b, new_size, state)
            }

            // Now handle neutrals as directed by the unfolding state
            // If possible, try approximate conversion checking, unfolding if it fails (and if that's allowed)
            (Val::Neutral(a), Val::Neutral(b)) if state.try_approx() && a.head() == b.head() => {
                let err = match self.unify_spines(a.spine(), b.spine(), size, state.spine_mode()) {
                    Ok(true) => return Ok(()),
                    e => e,
                };
                let a = Val::Neutral(a);
                let b = Val::Neutral(b);
                match state.approx_fail_mode() {
                    Some(state) => self.unify(a, b, size, state),
                    // don't try unfolded
                    None => Err(match err {
                        Ok(_) => UnifyError::Conversion(
                            a.quote(size, Some(&self.meta_cxt)),
                            b.quote(size, Some(&self.meta_cxt)),
                        ),
                        Err(e) => e,
                    }),
                }
            }

            // We want to prioritize solving the later meta first so it depends on the earlier meta
            (Val::Neutral(a), Val::Neutral(b)) if matches!((a.head(), b.head()), (Head::Var(Var::Meta(a)), Head::Var(Var::Meta(b))) if a < b) => {
                self.unify(Val::Neutral(b), Val::Neutral(a), size, state)
            }

            // There are multiple cases for two neutrals which need to be handled in sequence
            // basically we need to try one after another and they're not simple enough to disambiguate with guards
            (Val::Neutral(mut a), Val::Neutral(mut b)) => {
                // Try solving metas; if both are metas, solve whichever is possible
                if state.can_solve_metas() && a.head() != b.head() {
                    if let Head::Var(Var::Meta(m)) = a.head() {
                        if !self.meta_cxt.is_solved(m) {
                            let bc = match b.head() {
                                Head::Var(Var::Meta(m)) if !self.meta_cxt.is_solved(m) => {
                                    Some((m, b.spine().clone(), a.clone()))
                                }
                                _ => None,
                            };
                            match self
                                .meta_cxt
                                .solve(size, m, a.into_parts().1, Val::Neutral(b))
                            {
                                Ok(()) => return Ok(()),
                                Err(e) => match bc {
                                    Some((m, bsp, a)) if !self.meta_cxt.is_solved(m) => {
                                        match self.meta_cxt.solve(size, m, bsp, Val::Neutral(a)) {
                                            Ok(()) => return Ok(()),
                                            Err(_) => return Err(UnifyError::MetaSolve(e)),
                                        }
                                    }
                                    _ => return Err(UnifyError::MetaSolve(e)),
                                },
                            }
                        }
                    }
                    if let Head::Var(Var::Meta(m)) = b.head() {
                        if !self.meta_cxt.is_solved(m) {
                            return self
                                .meta_cxt
                                .solve(size, m, b.into_parts().1, Val::Neutral(a))
                                .map_err(UnifyError::MetaSolve);
                        }
                    }
                }

                // Unfold as much as possible first
                if state.can_unfold() {
                    // TODO allow inlining local definitions
                    match a.resolve(&mut Env::new(size), &self.meta_cxt) {
                        Ok(a) => return self.unify(a, Val::Neutral(b), size, state),
                        Err(a2) => a = a2,
                    }
                    match b.resolve(&mut Env::new(size), &self.meta_cxt) {
                        Ok(b) => return self.unify(Val::Neutral(a), b, size, state),
                        Err(b2) => b = b2,
                    }
                }

                // Unfolding isn't possible, so match heads and spines
                if a.head() == b.head()
                    && self.unify_spines(a.spine(), b.spine(), size, state.spine_mode())?
                {
                    Ok(())
                } else {
                    Err(UnifyError::Conversion(
                        Val::Neutral(a).quote(size, Some(&self.meta_cxt)),
                        Val::Neutral(b).quote(size, Some(&self.meta_cxt)),
                    ))
                }
            }

            // If only one side is a solvable meta, solve without unfolding the other side
            (Val::Neutral(n), x) | (x, Val::Neutral(n))
                if state.can_solve_metas()
                    && matches!(n.head(), Head::Var(Var::Meta(m)) if !self.meta_cxt.is_solved(m)) =>
            {
                if let Head::Var(Var::Meta(m)) = n.head() {
                    self.meta_cxt
                        .solve(size, m, n.into_parts().1, x)
                        .map_err(UnifyError::MetaSolve)
                } else {
                    unreachable!()
                }
            }

            // If a neutral still hasn't unified with anything, try unfolding it if possible
            (Val::Neutral(n), x) | (x, Val::Neutral(n)) if state.can_unfold() => {
                match n.resolve(&mut Env::new(size), &self.meta_cxt) {
                    Ok(n) => self.unify(n, x, size, state),
                    Err(n) => Err(UnifyError::Conversion(
                        Val::Neutral(n).quote(size, Some(&self.meta_cxt)),
                        x.quote(size, Some(&self.meta_cxt)),
                    )),
                }
            }

            // Eta-expand if there's a lambda on one side
            (Val::Fun(clos), x) | (x, Val::Fun(clos)) if matches!(clos.class, Lam(_)) => {
                let new_size = size + clos.params.len();
                let elim = Elim::App(clos.class.icit().unwrap(), clos.synthesize_args(size));
                let a = clos.open(size);
                self.unify(a, x.app(elim, &mut Env::new(new_size)), new_size, state)
            }

            (a, b) => Err(UnifyError::Conversion(
                a.quote(size, Some(&self.meta_cxt)),
                b.quote(size, Some(&self.meta_cxt)),
            )),
        }
    }
}
