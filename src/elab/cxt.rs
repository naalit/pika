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
pub enum VarDef {
    Var(Var<Lvl>, Val),
    Def(Def),
}
impl VarDef {
    fn as_var(&self) -> Option<Var<Lvl>> {
        match self {
            VarDef::Var(v, _) => Some(*v),
            VarDef::Def(_) => None,
        }
    }
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
    names: Vec<LocalVarDef>,
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
    fn lookup(&self, scope_idx: usize, name: SName, db: &dyn Elaborator) -> Option<VarEntry> {
        match self {
            Scope::Prelude => PRELUDE_DEFS
                .get_or_init(|| prelude_defs(db))
                .get(&name.0)
                .cloned()
                .map(|x| VarEntry::new(x, name)),
            Scope::Namespace(n) => {
                let split = SplitId::Named(name.0);
                let def = db.def(n.def_loc(split));
                if let Some(_) = db.def_type(def) {
                    Some(VarEntry::new(VarDef::Def(def), name))
                } else {
                    None
                }
            }
            Scope::Local(l) => l.lookup(scope_idx, name),
        }
    }
}

impl LocalScope {
    fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val, deps: Vec<(RelSpan, Lvl)>) {
        // TODO we probably want to keep the spans
        self.names
            .push(LocalVarDef::new(name.0, VarDef::Var(var, ty), deps));
    }

    fn define_local(&mut self, name: SName, ty: Val, deps: Vec<(RelSpan, Lvl)>) {
        self.define(name, Var::Local(name, self.size.next_lvl()), ty, deps);
        self.size = self.size.inc();
    }

    fn lookup(&self, scope: usize, name: SName) -> Option<VarEntry> {
        self.names
            .iter()
            .enumerate()
            .rfind(|(_, d)| d.name == name.0)
            .map(|(i, _)| VarEntry::Local {
                name,
                scope,
                var: i,
            })
    }

    fn new(size: Size) -> Self {
        LocalScope {
            size,
            names: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalVarDef {
    name: Name,
    var: VarDef,
    moved: Option<RelSpan>,
    deps: Vec<(RelSpan, Lvl)>,
}
impl LocalVarDef {
    fn new(name: Name, var: VarDef, deps: Vec<(RelSpan, Lvl)>) -> Self {
        LocalVarDef {
            name,
            var,
            moved: None,
            deps,
        }
    }
}

pub enum VarEntry {
    Local {
        name: SName,
        scope: usize,
        var: usize,
    },
    Other {
        name: SName,
        var: VarDef,
    },
}

pub enum MoveError {
    Consumed(RelSpan),
    DepConsumed(RelSpan, Name),
    Borrowed(RelSpan),
    InvalidMove(Doc),
}
impl VarEntry {
    fn new(var: VarDef, name: SName) -> VarEntry {
        VarEntry::Other { name, var }
    }

    pub fn var(&self, cxt: &Cxt) -> Var<Lvl> {
        let (def, name) = match self {
            VarEntry::Local {
                name, scope, var, ..
            } => match &cxt.scopes[*scope] {
                Scope::Local(l) => (&l.names[*var].var, name),
                _ => unreachable!(),
            },
            VarEntry::Other { name, var } => (var, name),
        };
        match def {
            VarDef::Var(v, _) => v.with_sname(*name),
            VarDef::Def(d) => Var::Def(*name, *d),
        }
    }

    pub fn ty(&self, cxt: &Cxt) -> Val {
        let def = match self {
            VarEntry::Local { scope, var, .. } => match &cxt.scopes[*scope] {
                Scope::Local(l) => &l.names[*var].var,
                _ => unreachable!(),
            },
            VarEntry::Other { var, .. } => var,
        };
        match def {
            VarDef::Var(_, t) => t.clone(),
            VarDef::Def(d) => cxt
                .db
                .def_type(*d)
                .and_then(|x| x.result)
                .unwrap_or(Val::Error),
        }
    }

    pub fn deps<'a>(&self, cxt: &'a Cxt) -> Option<&'a Vec<(RelSpan, Lvl)>> {
        match self {
            VarEntry::Local { scope, var, .. } => match &cxt.scopes[*scope] {
                Scope::Local(l) => Some(&l.names[*var].deps),
                _ => unreachable!(),
            },
            VarEntry::Other { .. } => None,
        }
    }

    pub fn try_move(&mut self, cxt: &mut Cxt) -> Result<(), MoveError> {
        match self {
            VarEntry::Local {
                name, scope, var, ..
            } => match &mut cxt.scopes[*scope] {
                Scope::Local(l) => {
                    let entry = &mut l.names[*var];
                    match entry.moved {
                        Some(span) => Err(MoveError::Consumed(span)),
                        None => {
                            let l = entry.var.as_var().unwrap().as_local().unwrap();

                            for &(span, lvl) in &cxt.expr_dependencies {
                                if lvl == l {
                                    return Err(MoveError::Borrowed(span));
                                }
                            }
                            entry.moved = Some(name.1);
                            cxt.check_deps(self.deps(cxt).unwrap())
                        }
                    }
                }
                _ => unreachable!(),
            },
            VarEntry::Other {
                var: VarDef::Def(_),
                name,
            } => Err(MoveError::InvalidMove(
                Doc::start("Cannot move out of definition ")
                    .chain(name.pretty(cxt.db).style(Doc::COLOR1)),
            )),
            VarEntry::Other { var, .. } => Err(MoveError::InvalidMove(
                Doc::start("Cannot move out of ").debug(var),
            )),
        }
    }

    pub fn try_borrow(&self, cxt: &mut Cxt) -> Result<(), Option<MoveError>> {
        match self {
            VarEntry::Local { scope, var, .. } => match &cxt.scopes[*scope] {
                Scope::Local(l) => {
                    let entry = &l.names[*var];
                    match entry.moved {
                        Some(span) => Err(Some(MoveError::Consumed(span))),
                        None => {
                            cxt.check_deps(&entry.deps)?;
                            Ok(())
                        }
                    }
                }
                _ => unreachable!(),
            },

            VarEntry::Other { .. } => Err(None),
        }
    }
}

pub struct Cxt<'a> {
    pub db: &'a dyn Elaborator,
    scopes: Vec<Scope>,
    env: Env,
    errors: Vec<(Severity, TypeError, RelSpan)>,
    pub mcxt: MetaCxt<'a>,
    expr_dependencies: Vec<(RelSpan, Lvl)>,
}
impl Cxt<'_> {
    pub fn new(db: &dyn Elaborator, def_cxt: DefCxt) -> Cxt {
        let mut cxt = Cxt {
            db,
            env: Env::new(Size::zero()),
            scopes: def_cxt.scopes,
            errors: Vec::new(),
            mcxt: MetaCxt::new(db),
            expr_dependencies: Vec::new(),
        };
        cxt.env = Env::new(cxt.size());
        cxt
    }

    pub fn record_deps(&mut self) {
        self.expr_dependencies.clear()
    }
    pub fn finish_deps(&mut self) -> Vec<(RelSpan, Lvl)> {
        self.expr_dependencies.split_off(0)
    }
    pub fn add_dep(&mut self, span: RelSpan, var: Lvl) {
        self.expr_dependencies.push((span, var));
    }
    pub fn check_deps(&self, deps: &[(RelSpan, Lvl)]) -> Result<(), MoveError> {
        for &(_, l) in deps {
            let def = self.local_def(l);
            if let Some(span) = def.moved {
                return Err(MoveError::DepConsumed(span, def.name));
            }
        }
        Ok(())
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

    pub fn define_local(
        &mut self,
        name: SName,
        ty: Val,
        value: Option<Val>,
        deps: Vec<(RelSpan, Lvl)>,
    ) {
        self.scope_mut().unwrap().define_local(name, ty, deps);
        self.env.push(value);
    }

    pub fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val) {
        if matches!(var, Var::Local(_, _)) {
            panic!("Call define_local() for local variables!");
        }
        self.scope_mut().unwrap().define(name, var, ty, Vec::new());
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

    pub fn lookup(&self, name: SName) -> Option<VarEntry> {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, x)| x.lookup(i, name, self.db))
    }

    fn local_def(&self, lvl: Lvl) -> &LocalVarDef {
        self.scopes
            .iter()
            .find_map(|x| match x {
                Scope::Local(x) => x.names.iter().find_map(|x| match &x.var {
                    VarDef::Var(Var::Local(_, l), _) if *l == lvl => Some(x),
                    _ => None,
                }),
                _ => None,
            })
            .unwrap()
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
