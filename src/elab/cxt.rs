use atomic_once_cell::AtomicOnceCell;

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefCxt {
    scopes: Vec<Scope>,
}
impl DefCxt {
    pub fn global(file: File) -> Self {
        DefCxt {
            scopes: vec![Scope::Prelude, Scope::Namespace(Namespace::Global(file))],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum VarDef {
    Var(Var<Lvl>, Val),
    Def(Def),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Namespace {
    Global(File),
    Def(Def),
}
impl Namespace {
    fn def_loc(self, split: SplitId) -> DefLoc {
        match self {
            Namespace::Global(file) => DefLoc::Root(file, split),
            Namespace::Def(def) => DefLoc::Child(def, split),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Scope {
    Prelude,
    Namespace(Namespace),
    Local(LocalScope),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalScope {
    size: Size,
    names: Vec<(Name, VarDef)>,
}

static PRELUDE_DEFS: AtomicOnceCell<HashMap<Name, VarDef>> = AtomicOnceCell::new();

fn prelude_defs(db: &dyn Elaborator) -> HashMap<Name, VarDef> {
    HashMap::from_iter(
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
    )
}

impl Scope {
    fn lookup(&self, name: Name, db: &dyn Elaborator) -> Option<Cow<VarDef>> {
        match self {
            Scope::Prelude => PRELUDE_DEFS
                .get_or_init(|| prelude_defs(db))
                .get(&name)
                .map(Cow::Borrowed),
            Scope::Namespace(n) => {
                let split = SplitId::Named(name);
                let def = db.def(n.def_loc(split));
                if let Some(_) = db.def_type(def) {
                    Some(Cow::Owned(VarDef::Def(def)))
                } else {
                    None
                }
            }
            Scope::Local(l) => l.lookup(name).map(Cow::Borrowed),
        }
    }
}

impl LocalScope {
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
        LocalScope {
            size: Size::zero(),
            names: global_defs,
        }
    }

    fn new(size: Size) -> Self {
        LocalScope {
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
            scopes: def_cxt.scopes,
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
        self.scope_mut().unwrap().define_local(name, ty);
        self.env.push(value);
    }

    pub fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val) {
        if matches!(var, Var::Local(_, _)) {
            panic!("Call define_local() for local variables!");
        }
        self.scope_mut().unwrap().define(name, var, ty);
    }

    pub fn def_cxt(&self) -> DefCxt {
        DefCxt {
            scopes: self.scopes.clone(),
        }
    }

    pub fn emit_errors(&self) -> Vec<Error> {
        self.errors
            .iter()
            .map(|(severity, x, span)| x.to_error(*severity, *span, self.db))
            .collect()
    }

    pub fn size(&self) -> Size {
        self.scope().map_or(Size::zero(), |x| x.size)
    }

    fn scope(&self) -> Option<&LocalScope> {
        self.scopes.iter().rev().find_map(|x| match x {
            Scope::Local(l) => Some(l),
            _ => None,
        })
    }

    fn scope_mut(&mut self) -> Option<&mut LocalScope> {
        self.scopes.iter_mut().rev().find_map(|x| match x {
            Scope::Local(l) => Some(l),
            _ => None,
        })
    }

    pub fn push(&mut self) {
        self.scopes.push(Scope::Local(LocalScope::new(self.size())));
    }

    pub fn push_def_scope(&mut self, def: Def) {
        self.scopes.push(Scope::Namespace(Namespace::Def(def)));
    }

    pub fn pop(&mut self) {
        self.scopes.pop();
        self.env.reset_to_size(self.size());
    }

    pub fn lookup(&self, name: SName) -> Option<(Var<Lvl>, Val)> {
        self.scopes
            .iter()
            .rev()
            .find_map(|x| x.lookup(name.0, self.db))
            .map(|x| match x.into_owned() {
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
            .find_map(|x| match x {
                Scope::Local(x) => x.names.iter().find_map(|(_, x)| match x {
                    VarDef::Var(Var::Local(_, l), t) if *l == lvl => Some(t.clone()),
                    _ => None,
                }),
                _ => None,
            })
            .unwrap()
    }

    pub fn locals(&self) -> Vec<(Name, Lvl)> {
        self.scopes
            .iter()
            .flat_map(|x| match x {
                Scope::Local(x) => x
                    .names
                    .iter()
                    .filter_map(|(n, v)| match v {
                        VarDef::Var(Var::Local(_, l), _) => Some((*n, *l)),
                        _ => None,
                    })
                    .collect::<Vec<_>>(),
                _ => Vec::new(),
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
