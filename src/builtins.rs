use crate::common::*;
use crate::term::Term;

#[derive(Copy, Clone, Debug)]
pub struct Builtins {
    eff: (TypeId, StructId),
    pure: TagId,
    effect: TagId,
}

impl Builtins {
    pub fn all_names() -> Vec<&'static str> {
        vec!["Int", "Eff", "Pure", "Effect"]
    }

    pub fn create(db: &impl MainGroup, file: FileId) -> Self {
        let mut bindings = db.bindings_mut();
        let (tid, cids) = bindings.add_type("Eff", ["Pure", "Effect"].iter().copied());
        let sid = bindings.next_struct();

        // type Eff R E of
        //   Pure R
        //   Effect [a:] (E a) (fun a => Eff R E)

        // Ideally we wouldn't ever make `Term`s here, we would go straight to `Elab`s
        let eff = Spanned::empty(Term::Var(bindings.create("Eff")));
        db.add_mod(
            sid,
            file,
            &[
                (Spanned::empty(bindings.create("Pure")), {
                    let sr = bindings.create("R");
                    let se = bindings.create("E");
                    let r = Spanned::empty(Term::Var(sr));
                    let e = Spanned::empty(Term::Var(se));

                    // Pure : fun [R: Type] [E: fun Type => Type] R => Eff R E
                    let ty = Spanned::empty(Term::Fun(
                        false,
                        vec![
                            (
                                true,
                                Spanned::empty(Term::Binder(
                                    sr,
                                    Some(Spanned::empty(Term::Type(0))),
                                )),
                            ),
                            (
                                true,
                                Spanned::empty(Term::Binder(
                                    se,
                                    Some(Spanned::empty(Term::Fun(
                                        false,
                                        vec![(false, Spanned::empty(Term::Type(0)))],
                                        Spanned::empty(Term::Type(0)),
                                    ))),
                                )),
                            ),
                            (false, r.clone()),
                        ],
                        Spanned::empty(Term::App(Spanned::empty(Term::App(eff.clone(), r)), e)),
                    ));
                    Spanned::empty(Term::Cons(cids[0], ty))
                }),
                (Spanned::empty(bindings.create("Effect")), {
                    let sr = bindings.create("R");
                    let se = bindings.create("E");
                    let sa = bindings.create("a");
                    let r = Spanned::empty(Term::Var(sr));
                    let e = Spanned::empty(Term::Var(se));
                    let a = Spanned::empty(Term::Var(sa));

                    // Effect : fun [R: Type] [E: fun Type => Type] [a: Type] (E a) (fun a => Eff R E) => Eff R E
                    let ty = Spanned::empty(Term::Fun(
                        false,
                        vec![
                            (
                                true,
                                Spanned::empty(Term::Binder(
                                    sr,
                                    Some(Spanned::empty(Term::Type(0))),
                                )),
                            ),
                            (
                                true,
                                Spanned::empty(Term::Binder(
                                    se,
                                    Some(Spanned::empty(Term::Fun(
                                        false,
                                        vec![(false, Spanned::empty(Term::Type(0)))],
                                        Spanned::empty(Term::Type(0)),
                                    ))),
                                )),
                            ),
                            (
                                true,
                                Spanned::empty(Term::Binder(
                                    sa,
                                    Some(Spanned::empty(Term::Type(0))),
                                )),
                            ),
                            (false, Spanned::empty(Term::App(e.clone(), a.clone()))),
                            (
                                false,
                                Spanned::empty(Term::Fun(
                                    false,
                                    vec![(false, a)],
                                    Spanned::empty(Term::App(
                                        Spanned::empty(Term::App(eff.clone(), r.clone())),
                                        e.clone(),
                                    )),
                                )),
                            ),
                        ],
                        Spanned::empty(Term::App(Spanned::empty(Term::App(eff, r)), e)),
                    ));
                    Spanned::empty(Term::Cons(cids[1], ty))
                }),
            ],
        );
        Builtins {
            eff: (tid, sid),
            pure: cids[0],
            effect: cids[1],
        }
    }

    pub fn resolve(&self, r: RawSym, h: &(impl Scoped + HasDatabase)) -> Option<Elab> {
        let mut b = h.bindings();
        match b.resolve_raw(r) {
            "Int" => Some(Elab::Builtin(Builtin::Int)),
            // Eff : fun (R: Type) (E: fun Type => Type) => Type
            "Eff" => Some(Elab::Data(
                self.eff.0,
                self.eff.1,
                Box::new(Elab::Fun(
                    Clos::default(),
                    Box::new(Elab::Type(0)),
                    Box::new(Elab::Fun(
                        Clos::default(),
                        Box::new(Elab::Fun(
                            Clos::default(),
                            Box::new(Elab::Type(0)),
                            Box::new(Elab::Type(0)),
                        )),
                        Box::new(Elab::Type(0)),
                    )),
                )),
            )),
            "Pure" | "Effect" => {
                // This is needed so we don't get a deadlock in `elab()`
                drop(b);
                let sid = self.eff.1;
                let scope = ScopeId::Struct(sid, Box::new(ScopeId::File(0)));
                let sym = **h
                    .database()
                    .symbols(scope.clone())
                    .iter()
                    .find(|s| s.raw() == r)
                    .unwrap();
                Some(
                    h.database()
                        .elab(scope, sym)
                        .unwrap()
                        .cloned(&mut Cloner::new(h)),
                )
            }
            _ => None,
        }
    }
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq, PartialOrd)]
pub enum Builtin {
    Int,
    Add,
    Sub,
    Mul,
    Div,
}
impl Builtin {
    pub fn is_binop(&self) -> bool {
        match self {
            Builtin::Sub | Builtin::Mul | Builtin::Div | Builtin::Add => true,
            _ => false,
        }
    }

    pub fn get_type(&self) -> Elab {
        match self {
            Builtin::Int => Elab::Type(0),
            Builtin::Sub | Builtin::Mul | Builtin::Div | Builtin::Add => Elab::Fun(
                Clos::default(),
                Box::new(Elab::Builtin(Builtin::Int)),
                Box::new(Elab::Fun(
                    Clos::default(),
                    Box::new(Elab::Builtin(Builtin::Int)),
                    Box::new(Elab::Builtin(Builtin::Int)),
                )),
            ),
        }
    }
}

impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Builtin::Int => write!(f, "Int"),
            Builtin::Add => write!(f, "(+)"),
            Builtin::Sub => write!(f, "(-)"),
            Builtin::Mul => write!(f, "(*)"),
            Builtin::Div => write!(f, "(/)"),
        }
    }
}
