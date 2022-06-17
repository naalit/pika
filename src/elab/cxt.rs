use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefCxt {
    scopes: Vec<ScopeState>,
}
impl DefCxt {
    pub fn global() -> Self {
        DefCxt {
            scopes: vec![Scope::global().state()],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ScopeState {
    global: bool,
    size: Size,
    names: Vec<(Name, (Var<Lvl>, Val))>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Scope {
    global: bool,
    size: Size,
    names: HashMap<Name, (Var<Lvl>, Val)>,
}
impl Scope {
    fn state(&self) -> ScopeState {
        ScopeState {
            global: self.global,
            size: self.size,
            names: self
                .names
                .iter()
                .map(|(a, b)| (a.clone(), b.clone()))
                .collect(),
        }
    }

    fn from_state(state: ScopeState) -> Scope {
        Scope {
            global: state.global,
            size: state.size,
            names: HashMap::from_iter(state.names),
        }
    }

    fn define(&mut self, name: Name, var: Var<Lvl>, ty: Val) {
        self.names.insert(name, (var, ty));
    }

    fn define_local(&mut self, name: Name, ty: Val) {
        self.define(name, Var::Local(name, self.size.next_lvl()), ty);
        self.size = self.size.inc();
    }

    fn global() -> Self {
        Scope {
            global: true,
            size: Size::zero(),
            names: HashMap::new(),
        }
    }

    fn new(size: Size) -> Self {
        Scope {
            global: false,
            size,
            names: HashMap::new(),
        }
    }
}

pub struct Cxt<'a> {
    pub db: &'a dyn Elaborator,
    scopes: Vec<Scope>,
    env: Env,
    errors: Vec<Spanned<TypeError>>,
    pub mcxt: MetaCxt,
}
impl Cxt<'_> {
    pub fn new(db: &dyn Elaborator, def_cxt: DefCxt) -> Cxt {
        let mut cxt = Cxt {
            db,
            env: Env::new(Size::zero()),
            scopes: def_cxt.scopes.into_iter().map(Scope::from_state).collect(),
            errors: Vec::new(),
            mcxt: MetaCxt::new(),
        };
        cxt.env = Env::new(cxt.size());
        cxt
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

    pub fn define_local(&mut self, name: Name, ty: Val, value: Option<Val>) {
        self.scope_mut().define_local(name, ty);
        self.env.push(value);
    }

    pub fn def_cxt(&self) -> DefCxt {
        DefCxt {
            scopes: self.scopes.iter().map(Scope::state).collect(),
        }
    }

    pub fn emit_errors(&self) -> Vec<Error> {
        self.errors
            .iter()
            .map(|(x, span)| x.to_error(span.clone(), self.db))
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

    pub fn lookup(&self, name: Name) -> Option<(Var<Lvl>, Val)> {
        self.scopes
            .iter()
            .rev()
            .find_map(|x| x.names.get(&name).cloned())
    }

    pub fn error(&mut self, span: RelSpan, error: TypeError) {
        self.errors.push((error, span));
    }
}
