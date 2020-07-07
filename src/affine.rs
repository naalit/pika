use crate::{common::*, term::Builtin};

pub struct ACtx<'a> {
    /// Multiplicity is specified as how many copies of the input are required per copy of the output.
    /// So if the output multiplicity is 0, for example, we can use things as much as we want.
    rmult: Mult,
    // TODO track spans on the elab
    moved: Vec<(Span, Sym)>,
    scope: ScopeId,
    database: &'a dyn MainGroupP,
}
impl<'a> ACtx<'a> {
    pub fn new(db: &'a (impl Scoped + HasDatabase)) -> Self {
        ACtx {
            scope: db.scope(),
            database: db.database(),
            moved: Vec::new(),
            rmult: Mult::Many,
        }
    }

    /// Temporarily lowers the return multiplicity for the duration of the closure.
    /// Only lowers it - `ACtx{ rmult: Zero .. }.with_rmult(One, |actx| actx.rmult) == Zero`.
    fn with_rmult<R>(&mut self, rmult: Mult, f: impl FnOnce(&mut ACtx<'a>) -> R) -> R {
        let old = self.rmult;
        self.rmult = self.rmult.min(rmult);
        let r = f(self);
        self.rmult = old;
        r
    }
}
impl<'a> HasBindings for ACtx<'a> {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.database.bindings_ref()
    }
}
impl<'a> HasDatabase for ACtx<'a> {
    fn database(&self) -> &dyn MainGroupP {
        self.database
    }
}
impl<'a> Scoped for ACtx<'a> {
    fn scope(&self) -> ScopeId {
        self.scope.clone()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Mult {
    Zero,
    One,
    Many,
}

impl Elab {
    /// This is a type. What's the multiplicity of its values?
    pub fn multiplicity(&self, env: &(impl Scoped + HasDatabase)) -> Mult {
        use Mult::*;
        // We know here that it's not erased
        match self {
            // Functions are never erased, at least for now
            Elab::Fun(cl, _, _) => {
                if cl.is_move {
                    One
                } else {
                    Many
                }
            }
            // Structs inherit multiplicity 1 from their members, but not 0
            // We would be duplicating the member if we duplicated the struct, but with 0 we didn't have any anyway
            Elab::StructInline(v) => v
                .iter()
                .map(|(_, x)| match x.multiplicity(env) {
                    Zero => Many,
                    x => x,
                })
                .min()
                .unwrap(),
            // TODO let the user control data type multiplicities
            Elab::Data(_, _, t) => {
                if **t == Elab::Type(0) {
                    One
                } else {
                    Zero
                }
            }
            Elab::Unit => Many,
            Elab::Binder(_, t) => t.multiplicity(env),
            Elab::Cons(_, t) => t.multiplicity(env),
            Elab::I32(_) => Many,
            Elab::Builtin(Builtin::Int) => Many,
            Elab::App(f, x) => {
                // Again, they're always at least 1
                f.multiplicity(env).min(x.multiplicity(env)).max(One)
            }
            Elab::Pair(x, y) => x.multiplicity(env).min(y.multiplicity(env)),
            Elab::Union(v) => v.iter().map(|x| x.multiplicity(env)).min().unwrap(),
            // In these two we know it's not concrete, but it's not erased, so it must be at least 1
            Elab::Var(_, _, _) => One,
            Elab::Project(_, _) => One,
            // Can't exist, so you can copy it I guess
            Elab::Bottom => Many,
            Elab::Block(_) | Elab::CaseOf(_, _, _) => panic!("not in WHNF!"),
            Elab::StructIntern(_) => {
                unreachable!("Right now, we always make a new struct for types")
            }
            Elab::Builtin(_) => Many,
            Elab::Top => Zero,
            Elab::Type(_) => Zero,
        }
    }

    pub fn check_affine(&self, actx: &mut ACtx) -> Result<(), Error> {
        let old = actx.rmult;
        let ty = self.get_type(actx);
        let mult = ty.multiplicity(actx);
        actx.rmult = old.min(mult);

        use Mult::*;
        match self {
            Elab::Var(use_span, s, _) => {
                if actx.rmult != Zero {
                    match mult {
                        One => {
                            if let Some((moved_span, _)) = actx.moved.iter().find(|(_, x)| *x == *s) {
                                return Err(Error::new(
                                    actx.scope.file(),
                                    Doc::start("Type error: use of moved value ").chain(s.pretty(actx)),
                                    *use_span,
                                    "use of moved value")
                                .with_label(
                                    actx.scope.file(),
                                    *moved_span,
                                    "value moved here".to_string())
                                );
                            } else {
                                actx.moved.push((*use_span, *s));
                            }
                        }
                        // This is actually impossible: if `mult` was Zero, `actx.rmult` would be Zero
                        Zero => todo!("unreachable: Type(?) error: use of erased value {} in non-erased context", s.pretty(actx).ansi_string()),
                        Many => (),
                    }
                }
            }
            Elab::Binder(_, t) => t.check_affine(actx)?,
            Elab::Cons(_, t) => t.check_affine(actx)?,
            Elab::Fun(cl, from, to) => {
                if !cl.is_move {
                    for (k, v) in cl.tys.iter() {
                        if v.multiplicity(actx) == One {
                            return Err(Error::new(
                                actx.scope.file(),
                                Doc::start("non-")
                                    .chain(Doc::start("move").style(Style::Keyword))
                                    .add(" closure captures move-only value ")
                                    .chain(k.pretty(actx))
                                    .add(", of type '")
                                    .chain(v.pretty(actx).add("'").group().style(Style::Bold)),
                                cl.span,
                                "captures move-only value",
                            ));
                        }
                    }
                }
                actx.with_rmult(Zero, |actx| from.check_affine(actx))?;
                to.check_affine(actx)?;
            }
            Elab::CaseOf(val, cases, _) => {
                val.check_affine(actx)?;
                for (pat, body) in cases {
                    // TODO `Pat::check_affine`?
                    body.check_affine(actx)?;
                }
            }
            Elab::App(x, y) | Elab::Pair(x, y) => {
                x.check_affine(actx)?;
                y.check_affine(actx)?;
            }
            // When we call `elab()` on each member, we'll check it
            // And we know it can't use local variables, so it won't matter what's in `actx`
            Elab::StructIntern(_) | Elab::Data(_, _, _) => (),
            Elab::StructInline(v) => {
                for (_, x) in v {
                    x.check_affine(actx)?;
                }
            }
            Elab::Project(r, m) => {
                r.check_affine(actx)?;
                if actx.rmult != Zero {
                    match mult {
                        One => todo!("Track moved struct fields?"),
                        Zero => todo!("unreachable: Type(?) error: use of erased struct field {} in non-erased context", m.pretty(actx).ansi_string()),
                        Many => (),
                    }
                }
            }
            Elab::Block(v) => {
                for e in v {
                    match e {
                        ElabStmt::Def(_, e) => e.check_affine(actx)?,
                        ElabStmt::Expr(e) => e.check_affine(actx)?,
                    }
                }
            }
            Elab::Union(v) => {
                for i in v {
                    i.check_affine(actx)?;
                }
            }
            Elab::Builtin(_)
            | Elab::I32(_)
            | Elab::Type(_)
            | Elab::Bottom
            | Elab::Top
            | Elab::Unit => (),
        }

        actx.rmult = old;
        Ok(())
    }
}
