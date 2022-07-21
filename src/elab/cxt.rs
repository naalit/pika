use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefCxt {
    scopes: Vec<ScopeState>,
}
impl DefCxt {
    pub fn global(file: File) -> Self {
        DefCxt {
            scopes: vec![ScopeState::Global(file)],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum VarDef {
    Var(Var<Lvl>, Val),
    Def(Def),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum ScopeState {
    Global(File),
    Local {
        size: Size,
        names: Vec<(Name, VarDef)>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Scope {
    size: Size,
    names: Vec<(Name, VarDef)>,
}

impl Scope {
    fn state(&self) -> ScopeState {
        ScopeState::Local {
            size: self.size,
            names: self
                .names
                .iter()
                .map(|(a, b)| (a.clone(), b.clone()))
                .collect(),
        }
    }

    fn from_state(state: ScopeState, db: &dyn Elaborator) -> Scope {
        match state {
            ScopeState::Local { size, names } => Scope { size, names },
            ScopeState::Global(file) => Scope::global(db, file),
        }
    }

    fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val) {
        // TODO we probably want to keep the spans
        self.names.push((name.0, VarDef::Var(var, ty)));
    }

    fn define_local(&mut self, name: SName, ty: Val) {
        self.define(name, Var::Local(name, self.size.next_lvl()), ty);
        self.size = self.size.inc();
    }

    fn lookup(&self, name: Name) -> Option<&VarDef> {
        self.names
            .iter()
            .rfind(|&&(n, _)| n == name)
            .map(|(_, d)| d)
    }

    fn global(db: &(impl Elaborator + ?Sized), file: File) -> Self {
        let mut global_defs = Vec::from_iter(
            [
                ("I8", Builtin::IntType(IntType::I8), Val::Type),
                ("I16", Builtin::IntType(IntType::I16), Val::Type),
                ("I32", Builtin::IntType(IntType::I32), Val::Type),
                ("I64", Builtin::IntType(IntType::I64), Val::Type),
                ("U8", Builtin::IntType(IntType::U8), Val::Type),
                ("U16", Builtin::IntType(IntType::U16), Val::Type),
                ("U32", Builtin::IntType(IntType::U32), Val::Type),
                ("U64", Builtin::IntType(IntType::U64), Val::Type),
            ]
            .iter()
            .map(|(k, v, t)| {
                (
                    db.name(k.to_string()),
                    VarDef::Var(Var::Builtin(*v), t.clone()),
                )
            }),
        );
        for split in db.all_split_ids(file) {
            let def = db.def(DefLoc::Root(file, split));
            if let Some(name) = db.def_name(def) {
                global_defs.push((name, VarDef::Def(def)));
            }
        }
        Scope {
            size: Size::zero(),
            names: global_defs,
        }
    }

    fn new(size: Size) -> Self {
        Scope {
            size,
            names: Vec::new(),
        }
    }
}

pub struct Cxt<'a> {
    pub db: &'a dyn Elaborator,
    scopes: Vec<Scope>,
    env: Env,
    errors: Vec<(Severity, TypeError, RelSpan)>,
    pub mcxt: MetaCxt<'a>,
}
impl Cxt<'_> {
    pub fn new(db: &dyn Elaborator, def_cxt: DefCxt) -> Cxt {
        let mut cxt = Cxt {
            db,
            env: Env::new(Size::zero()),
            scopes: def_cxt
                .scopes
                .into_iter()
                .map(|x| Scope::from_state(x, db))
                .collect(),
            errors: Vec::new(),
            mcxt: MetaCxt::new(db),
        };
        cxt.env = Env::new(cxt.size());
        cxt
    }

    pub fn unify(
        &mut self,
        inferred: Val,
        expected: Val,
        reason: &CheckReason,
    ) -> Result<(), super::unify::UnifyError> {
        self.mcxt
            .unify(inferred, expected, self.size(), self.env(), reason)
    }

    pub fn env(&self) -> Env {
        if self.env.size != self.size() {
            panic!(
                "env size {:?}, but self.size() {:?}",
                self.env.size,
                self.size()
            );
        }
        self.env.clone()
    }

    pub fn set_env(&mut self, env: Env) {
        assert_eq!(env.size, self.size());
        self.env = env;
    }

    pub fn define_local(&mut self, name: SName, ty: Val, value: Option<Val>) {
        self.scope_mut().define_local(name, ty);
        self.env.push(value);
    }

    pub fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val) {
        if matches!(var, Var::Local(_, _)) {
            panic!("Call define_local() for local variables!");
        }
        self.scope_mut().define(name, var, ty);
    }

    pub fn def_cxt(&self) -> DefCxt {
        DefCxt {
            scopes: self.scopes.iter().map(Scope::state).collect(),
        }
    }

    pub fn emit_errors(&self) -> Vec<Error> {
        self.errors
            .iter()
            .map(|(severity, x, span)| x.to_error(*severity, *span, self.db))
            .collect()
    }

    pub fn size(&self) -> Size {
        self.scopes.last().unwrap().size
    }

    fn scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    fn scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    pub fn push(&mut self) {
        self.scopes.push(Scope::new(self.size()));
    }

    pub fn pop(&mut self) {
        self.scopes.pop();
        self.env.reset_to_size(self.size());
    }

    pub fn lookup(&self, name: SName) -> Option<(Var<Lvl>, Val)> {
        self.scopes
            .iter()
            .rev()
            .find_map(|x| x.lookup(name.0).cloned())
            .map(|x| match x {
                VarDef::Var(v, t) => (v.with_sname(name), t),
                VarDef::Def(d) => (
                    Var::Def(name, d),
                    self.db
                        .def_type(d)
                        .and_then(|x| x.result)
                        .unwrap_or(Val::Error),
                ),
            })
    }

    pub fn local_ty(&self, lvl: Lvl) -> Val {
        self.scopes
            .iter()
            .find_map(|x| {
                x.names.iter().find_map(|(_, x)| match x {
                    VarDef::Var(Var::Local(_, l), t) if *l == lvl => Some(t.clone()),
                    _ => None,
                })
            })
            .unwrap()
    }

    pub fn locals(&self) -> Vec<(Name, Lvl)> {
        self.scopes
            .iter()
            .flat_map(|x| {
                x.names.iter().filter_map(|(n, v)| match v {
                    VarDef::Var(Var::Local(_, l), _) => Some((*n, *l)),
                    _ => None,
                })
            })
            .collect()
    }

    pub fn error(&mut self, span: RelSpan, error: impl Into<TypeError>) {
        self.errors.push((Severity::Error, error.into(), span));
    }

    pub fn warning(&mut self, span: RelSpan, error: impl Into<TypeError>) {
        self.errors.push((Severity::Warning, error.into(), span));
    }
}
