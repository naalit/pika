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
    names: Vec<VarEntryDef>,
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
    fn lookup(&mut self, name: SName, db: &dyn Elaborator) -> Option<VarEntry> {
        match self {
            Scope::Prelude => PRELUDE_DEFS
                .get_or_init(|| prelude_defs(db))
                .get(&name.0)
                .map(Cow::Borrowed)
                .map(|x| VarEntry::new(x, name)),
            Scope::Namespace(n) => {
                let split = SplitId::Named(name.0);
                let def = db.def(n.def_loc(split));
                if let Some(_) = db.def_type(def) {
                    Some(VarEntry::new(Cow::Owned(VarDef::Def(def)), name))
                } else {
                    None
                }
            }
            Scope::Local(l) => l.lookup(name),
        }
    }
}

impl LocalScope {
    fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val) {
        // TODO we probably want to keep the spans
        self.names
            .push(VarEntryDef::new(name.0, VarDef::Var(var, ty)));
    }

    fn define_local(&mut self, name: SName, ty: Val) {
        self.define(name, Var::Local(name, self.size.next_lvl()), ty);
        self.size = self.size.inc();
    }

    fn lookup(&mut self, name: SName) -> Option<VarEntry> {
        self.names
            .iter_mut()
            .rfind(|d| d.name == name.0)
            .map(|d| d.entry(name))
    }

    fn new(size: Size) -> Self {
        LocalScope {
            size,
            names: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct VarEntryDef {
    name: Name,
    var: VarDef,
    moved: Option<RelSpan>,
}
impl VarEntryDef {
    fn new(name: Name, var: VarDef) -> Self {
        VarEntryDef {
            name,
            var,
            moved: None,
        }
    }
    fn entry(&mut self, name: SName) -> VarEntry {
        VarEntry {
            name,
            var: Cow::Borrowed(&self.var),
            moved: Some(&mut self.moved),
        }
    }
}

pub struct VarEntry<'a> {
    name: SName,
    var: Cow<'a, VarDef>,
    moved: Option<&'a mut Option<RelSpan>>,
}
impl VarEntry<'_> {
    fn new(var: Cow<VarDef>, name: SName) -> VarEntry {
        VarEntry {
            name,
            var,
            moved: None,
        }
    }

    pub fn var(&self) -> Var<Lvl> {
        match &*self.var {
            VarDef::Var(v, _) => v.with_sname(self.name),
            VarDef::Def(d) => (Var::Def(self.name, *d)),
        }
    }

    pub fn ty(&self, db: &dyn Elaborator) -> Val {
        match &*self.var {
            VarDef::Var(_, t) => t.clone(),
            VarDef::Def(d) => db.def_type(*d).and_then(|x| x.result).unwrap_or(Val::Error),
        }
    }

    pub fn try_move(&mut self) -> Result<(), RelSpan> {
        match &mut self.moved {
            Some(old) => match *old {
                Some(old) => Err(*old),
                None => {
                    **old = Some(self.name.1);
                    Ok(())
                }
            },
            None => panic!("Not a movable type of definition?"),
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

    pub fn lookup(&mut self, name: SName) -> Option<VarEntry> {
        self.scopes
            .iter_mut()
            .rev()
            .find_map(|x| x.lookup(name, self.db))
    }

    pub fn local_ty(&self, lvl: Lvl) -> Val {
        self.scopes
            .iter()
            .find_map(|x| match x {
                Scope::Local(x) => x.names.iter().find_map(|x| match &x.var {
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
                    .filter_map(|x| match &x.var {
                        VarDef::Var(Var::Local(_, l), _) => Some((x.name, *l)),
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
