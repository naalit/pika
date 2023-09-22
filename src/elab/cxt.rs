use std::{num::NonZeroU64, rc::Rc};

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefCxt {
    scopes: Vec<Scope>,
    n_borrows: u64,
}
impl DefCxt {
    pub fn global(file: File) -> Self {
        DefCxt {
            scopes: vec![Scope::Prelude, Scope::Namespace(Namespace::Global(file))],
            n_borrows: 0,
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
    start_size: Size,
    names: Vec<LocalVarDef>,
    captures: Option<Vec<(Lvl, (CopyClass, Access))>>,
}

pub fn prelude_defs(db: &dyn Elaborator) -> std::sync::Arc<HashMap<Name, VarDef>> {
    std::sync::Arc::new(HashMap::from_iter(
        [
            ("I8", Builtin::IntType(IntType::I8), Val::Type),
            ("I16", Builtin::IntType(IntType::I16), Val::Type),
            ("I32", Builtin::IntType(IntType::I32), Val::Type),
            ("I64", Builtin::IntType(IntType::I64), Val::Type),
            ("U8", Builtin::IntType(IntType::U8), Val::Type),
            ("U16", Builtin::IntType(IntType::U16), Val::Type),
            ("U32", Builtin::IntType(IntType::U32), Val::Type),
            ("U64", Builtin::IntType(IntType::U64), Val::Type),
            ("Str", Builtin::StringType, Val::Type),
        ]
        .iter()
        .map(|(k, v, t)| {
            (
                db.name(k.to_string()),
                VarDef::Var(Var::Builtin(*v), t.clone()),
            )
        }),
    ))
}

impl Scope {
    fn lookup(&self, scope_idx: usize, name: SName, db: &dyn Elaborator) -> Option<VarEntry> {
        match self {
            Scope::Prelude => db
                .prelude_defs()
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
    fn define(
        &mut self,
        name: SName,
        var: Var<Lvl>,
        ty: Val,
        borrow: Option<Borrow>,
        mutable: bool,
    ) {
        // TODO we probably want to keep the spans
        self.names.push(LocalVarDef::new(
            name.0,
            VarDef::Var(var, ty),
            borrow,
            mutable,
        ));
    }

    fn define_local(&mut self, name: SName, ty: Val, borrow: Borrow, mutable: bool) {
        self.define(
            name,
            Var::Local(name, self.size.next_lvl()),
            ty,
            Some(borrow),
            mutable,
        );
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

    fn new(size: Size, capture: bool) -> Self {
        LocalScope {
            size,
            start_size: size,
            names: Vec::new(),
            captures: capture.then(|| Vec::new()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BorrowInvalid {
    skip_borrow: Option<Borrow>,
    base_access: Access,
    chain_start: Option<Access>,
    chain_end: Option<Access>,
    move_type: Option<Rc<Expr>>,
}
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct BorrowDef {
    mutable_parents: HashMap<Borrow, Access>,
    /// Only one mutable borrow can be active at once, but there could still be multiple entries here if it gets mutably
    /// borrowed separately in two different case branches
    mutable_borrows: HashMap<Borrow, Access>,
    immutable_borrows: HashMap<Borrow, Access>,
    /// These are borrows that don't borrow this one, but do depend on it by-value - so if this gets invalidated, they will too
    move_or_copy: HashMap<Borrow, Access>,
    invalid: Option<BorrowInvalid>,
}
impl BorrowDef {
    fn merge_with(&mut self, other: BorrowDef) -> Option<BorrowInvalid> {
        let was_valid = self.invalid.is_none();
        let other_valid = other.invalid.is_none();
        if was_valid {
            self.invalid = other.invalid;
        }
        self.mutable_borrows.extend(other.mutable_borrows);
        self.immutable_borrows.extend(other.immutable_borrows);
        self.move_or_copy.extend(other.move_or_copy);
        self.mutable_parents.extend(other.mutable_parents);
        if was_valid || other_valid {
            // It got invalidated in only one of the branches, invalidate it again now
            self.invalid.clone()
        } else {
            // If it's invalid now, it already was in both branches so we don't care
            None
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum AccessKind {
    Mut,
    Imm,
    Move,
    Copy,
}
impl AccessKind {
    pub fn borrow(mutable: bool) -> Self {
        if mutable {
            AccessKind::Mut
        } else {
            AccessKind::Imm
        }
    }
    pub fn copy_move(copy: bool) -> Self {
        if copy {
            AccessKind::Copy
        } else {
            AccessKind::Move
        }
    }
}
impl From<CopyClass> for AccessKind {
    fn from(value: CopyClass) -> Self {
        match value {
            CopyClass::Move => AccessKind::Move,
            CopyClass::Copy => AccessKind::Copy,
            CopyClass::Mut => AccessKind::Mut,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Borrow(NonZeroU64);
impl Borrow {
    fn new(cxt: &mut Cxt) -> Borrow {
        cxt.borrows.push(BorrowDef::default());
        Borrow(
            (cxt.borrows_start + cxt.borrows.len() as u64)
                .try_into()
                .unwrap(),
        )
    }

    fn def_mut<'a>(self, cxt: &'a mut Cxt) -> Option<&'a mut BorrowDef> {
        if self.0.get() <= cxt.borrows_start {
            return None;
        }
        let idx = self.0.get() - cxt.borrows_start - 1;
        cxt.borrows.get_mut(idx as usize)
    }
    fn def<'a>(self, cxt: &'a Cxt) -> Option<&'a BorrowDef> {
        if self.0.get() <= cxt.borrows_start {
            return None;
        }
        let idx = self.0.get() - cxt.borrows_start - 1;
        cxt.borrows.get(idx as usize)
    }

    pub fn mutable_dependencies(self, cxt: &Cxt) -> Vec<(Borrow, Access)> {
        self.def(cxt)
            .map(|d| d.mutable_parents.iter().map(|(&x, &y)| (x, y)).collect())
            .unwrap_or_default()
    }

    fn invalidate(self, mut invalid: BorrowInvalid, cxt: &mut Cxt) {
        if invalid.skip_borrow == Some(self) {
            return;
        }
        if let Some(def) = self.def_mut(cxt) {
            if def.invalid.is_none()
                || def
                    .move_or_copy
                    .iter()
                    .any(|x| x.1.kind == AccessKind::Move)
            {
                let start = invalid.chain_start.is_none();
                if def.invalid.is_none() {
                    def.invalid = Some(invalid.clone());
                }
                for (i, a) in def
                    .immutable_borrows
                    .iter()
                    .chain(&def.move_or_copy)
                    .chain(&def.mutable_borrows)
                    .map(|(&x, &y)| (x, y))
                    .collect::<Vec<_>>()
                {
                    if start {
                        invalid.chain_start = Some(a);
                    } else {
                        invalid.chain_end = Some(a);
                    }
                    i.invalidate(invalid.clone(), cxt);
                }
            }
        }
    }
    fn invalidate_children(self, access: Access, cxt: &mut Cxt) {
        if let Some(def) = self.def_mut(cxt) {
            if def.invalid.is_none() {
                // Don't include move_or_copy - those are conceptually on the same level as this borrow, not children
                for (i, a) in def
                    .immutable_borrows
                    .iter()
                    .chain(&def.mutable_borrows)
                    .map(|(&x, &y)| (x, y))
                    .collect::<Vec<_>>()
                {
                    i.invalidate(
                        BorrowInvalid {
                            skip_borrow: Some(self),
                            base_access: access,
                            chain_start: Some(a),
                            chain_end: None,
                            move_type: None,
                        },
                        cxt,
                    );
                }
            }
        }
    }
    fn invalidate_mutable(self, access: Access, cxt: &mut Cxt) {
        if let Some(def) = self.def_mut(cxt) {
            if def.invalid.is_none() {
                for (i, a) in def.mutable_borrows.clone() {
                    i.invalidate(
                        BorrowInvalid {
                            skip_borrow: Some(self),
                            base_access: access,
                            chain_start: Some(a),
                            chain_end: None,
                            move_type: None,
                        },
                        cxt,
                    )
                }
            }
        }
    }
    fn invalidate_self(self, access: Access, move_type: Rc<Expr>, cxt: &mut Cxt) {
        self.invalidate(
            BorrowInvalid {
                skip_borrow: None,
                base_access: access,
                chain_start: None,
                chain_end: None,
                move_type: Some(move_type),
            },
            cxt,
        )
    }

    /// Does not check validity or invalidate old borrows - do that before calling this
    pub fn add_borrow(self, borrow: Borrow, access: Access, cxt: &mut Cxt) {
        if let Some(def) = self.def_mut(cxt) {
            match access.kind {
                AccessKind::Mut => {
                    def.mutable_borrows.insert(borrow, access);
                    if let Some(def) = borrow.def_mut(cxt) {
                        def.mutable_parents.insert(self, access);
                    }
                }
                AccessKind::Imm => {
                    def.immutable_borrows.insert(borrow, access);
                }
                AccessKind::Move => {
                    def.move_or_copy.insert(borrow, access);
                }
                AccessKind::Copy => {
                    def.move_or_copy.insert(borrow, access);
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalVarDef {
    name: Name,
    var: VarDef,
    borrow: Option<Borrow>,
    mutable: bool,
}
impl LocalVarDef {
    fn new(name: Name, var: VarDef, borrow: Option<Borrow>, mutable: bool) -> Self {
        LocalVarDef {
            name,
            var,
            borrow,
            mutable,
        }
    }
}

#[derive(Debug, Clone)]
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum AccessPoint {
    Expr,
    Name(Name),
    Function(Option<Name>),
}
impl From<Name> for AccessPoint {
    fn from(value: Name) -> Self {
        AccessPoint::Name(value)
    }
}
impl AccessPoint {
    fn pretty(
        &self,
        initial: bool,
        col: ariadne::Color,
        db: &(impl crate::elab::Elaborator + ?Sized),
    ) -> Doc {
        match self {
            AccessPoint::Expr => {
                Doc::start(if initial { "T" } else { "t" }).add("he result of this expression", ())
            }
            AccessPoint::Name(name) => {
                Doc::start(if initial { "Variable " } else { "" }).chain(name.pretty(db).style(col))
            }
            AccessPoint::Function(func) => Doc::start(if initial { "T" } else { "t" })
                .add("his call", ())
                .chain(match func {
                    Some(name) => Doc::start(" to ").chain(name.pretty(db).style(col)),
                    None => Doc::none(),
                }),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Access {
    pub kind: AccessKind,
    pub point: AccessPoint,
    pub span: RelSpan,
}
#[derive(Clone, Debug)]
pub struct AccessError {
    invalid_access: Access,
    dep_chain_start: Option<Access>,
    dep_chain_end: Option<Access>,
    dep_access: Access,
    move_type: Option<Rc<Expr>>,
}
impl AccessError {
    pub fn to_error(&self, severity: Severity, db: &dyn Elaborator) -> Error {
        let name0 = |i, swap| {
            self.dep_access
                .point
                .pretty(i, if swap { Doc::COLOR1 } else { Doc::COLOR2 }, db)
        };
        let name1 = |i, swap| {
            self.invalid_access
                .point
                .pretty(i, if swap { Doc::COLOR2 } else { Doc::COLOR1 }, db)
        };
        let dep =
            self.dep_access.point != self.invalid_access.point || self.dep_chain_start.is_some();
        let (message, dep_message, swap) = match self.dep_access.kind {
            AccessKind::Move => (
                if dep {
                    name1(true, false)
                        .add(" borrows ", ())
                        .chain(name0(false, false))
                        .add(" which has already been consumed", ())
                } else {
                    name1(true, false).add(" has already been consumed", ())
                },
                Doc::start("Variable ")
                    .chain(name0(false, false))
                    .add(" was consumed here", ()),
                false,
            ),
            _ if self
                .dep_chain_start
                .map_or(self.invalid_access.kind == AccessKind::Mut, |x| {
                    x.kind == AccessKind::Mut
                }) =>
            {
                (
                    name0(true, true).add(" cannot be accessed while mutably borrowed", ()),
                    Doc::start("Mutable borrow later used here"),
                    true,
                )
            }
            AccessKind::Mut => (
                name0(true, true).add(" cannot be accessed mutably while it is borrowed", ()),
                Doc::start("Borrow later used here"),
                true,
            ),
            _ => unreachable!(), // TODO can this ever happen?
        };

        let mut secondary = vec![Label {
            span: if swap {
                self.invalid_access.span
            } else {
                self.dep_access.span
            },
            message: dep_message,
            color: Some(Doc::COLOR2),
        }];
        if let Some(access) = self.dep_chain_start {
            let mutable = access.kind == AccessKind::Mut;
            secondary.push(Label {
                span: access.span,
                color: Some(Doc::COLOR3),
                message: name0(true, swap) // TODO should this use COLOR3?
                    .add(" was", ())
                    .add(if mutable { " mutably" } else { "" }, ())
                    .add(" borrowed here", ()),
            });
        }
        if let Some(access) = self.dep_chain_end {
            let mutable = self.dep_chain_start.unwrap().kind == AccessKind::Mut;
            secondary.push(Label {
                span: access.span,
                color: Some(Doc::COLOR4),
                message: match access.point {
                    AccessPoint::Function(_) => access
                        .point
                        .pretty(true, Doc::COLOR4, db)
                        .add(" could mutate ", ())
                        .chain(name1(false, swap))
                        .add(" and insert", ())
                        .add(if mutable { " mutably" } else { "" }, ())
                        .add(" borrowed data from ", ())
                        .chain(name0(false, swap)),
                    _ => name1(true, swap)
                        .add(if mutable { " mutably" } else { "" }, ())
                        .add(" borrows ", ())
                        .chain(name0(false, swap))
                        .add(" through ", ())
                        .chain(access.point.pretty(false, Doc::COLOR4, db)),
                },
            });
        }

        let note = if self.dep_access.kind == AccessKind::Move {
            self.move_type.as_ref().map(|ty| {
                Doc::start("Move occurs because ")
                    .chain(name0(false, swap))
                    .add(" has type '", ())
                    .chain(ty.pretty(db))
                    .add("' which cannot be copied implicitly", ())
            })
        } else {
            None
        };

        Error {
            severity,
            message: message.clone(),
            message_lsp: None,
            primary: Label {
                span: if swap {
                    self.dep_access.span
                } else {
                    self.invalid_access.span
                },
                message,
                color: Some(Doc::COLOR1),
            },
            secondary,
            note,
        }
    }
}

pub enum MoveError {
    AccessError(AccessError),
    InvalidMove(Doc, Name, Box<Expr>),
    InvalidBorrow(Doc, Name),
    FunAccess(Access, Expr, CheckReason),
    InvalidAccess(Doc, Access),
}
impl From<AccessError> for MoveError {
    fn from(value: AccessError) -> Self {
        MoveError::AccessError(value)
    }
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

    pub fn borrow(&self, cxt: &Cxt) -> Option<Borrow> {
        match self {
            VarEntry::Local { scope, var, .. } => match &cxt.scopes[*scope] {
                Scope::Local(l) => l.names[*var].borrow,
                _ => unreachable!(),
            },
            _ => None,
        }
    }

    pub fn mutable(&self, cxt: &Cxt) -> bool {
        match self {
            VarEntry::Local { scope, var, .. } => match &cxt.scopes[*scope] {
                Scope::Local(l) => l.names[*var].mutable,
                _ => unreachable!(),
            },
            _ => false,
        }
    }

    pub fn access(&self, kind: AccessKind) -> Access {
        let &(name, span) = match self {
            VarEntry::Local { name, .. } => name,
            VarEntry::Other { name, .. } => name,
        };
        Access {
            kind,
            point: name.into(),
            span,
        }
    }

    pub fn try_move(&self, ty: Expr, cxt: &mut Cxt) -> Result<(), MoveError> {
        if let Some(borrow) = self.borrow(cxt) {
            cxt.check_deps(borrow, self.access(AccessKind::Move))?;
        }
        match self {
            VarEntry::Local { scope, var, .. } => match &mut cxt.scopes[*scope] {
                Scope::Local(l) => {
                    let entry = &mut l.names[*var];
                    let lvl = entry.var.as_var().unwrap().as_local();
                    let access = self.access(AccessKind::Move);
                    entry
                        .borrow
                        .unwrap()
                        .invalidate_self(access, Rc::new(ty), cxt);
                    if let Some(lvl) = lvl {
                        cxt.record_access(lvl, access);
                    }
                    Ok(())
                }
                _ => unreachable!(),
            },
            VarEntry::Other {
                var: VarDef::Def(_),
                name,
            } => Err(MoveError::InvalidMove(
                Doc::start("Cannot move out of definition ")
                    .chain(name.pretty(cxt.db).style(Doc::COLOR1)),
                name.0,
                Box::new(ty),
            )),
            VarEntry::Other { var, name } => Err(MoveError::InvalidMove(
                Doc::start("Cannot move out of ").debug(var),
                name.0,
                Box::new(ty),
            )),
        }
    }

    pub fn try_borrow(
        &self,
        mutable: bool,
        mutable_access: bool,
        cxt: &mut Cxt,
    ) -> Result<(), MoveError> {
        match self {
            VarEntry::Local { scope, var, .. } => match &cxt.scopes[*scope] {
                Scope::Local(l) => {
                    let entry = &l.names[*var];
                    if mutable_access && !entry.mutable {
                        return Err(MoveError::InvalidBorrow(
                            Doc::start("Cannot mutate immutable variable ")
                                .chain(entry.name.pretty(cxt.db)),
                            entry.name,
                        ));
                    }
                    let access = self.access(AccessKind::borrow(mutable));
                    let borrow = entry.borrow.unwrap();
                    cxt.check_deps(borrow, access)?;

                    let lvl = entry.var.as_var().unwrap().as_local();
                    if mutable {
                        borrow.invalidate_children(access, cxt);
                    } else {
                        borrow.invalidate_mutable(access, cxt);
                    }
                    if let Some(lvl) = lvl {
                        cxt.record_access(lvl, access);
                    }
                    Ok(())
                }
                _ => unreachable!(),
            },
            // It's fine to borrow definitions immutably, they can't ever be mutated
            VarEntry::Other {
                var: VarDef::Def(_),
                ..
            } if !mutable => Ok(()),
            VarEntry::Other { var, name } => Err(MoveError::InvalidBorrow(
                Doc::start("Cannot move out of ").debug(var),
                name.0,
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub struct BorrowCheckpoint(Vec<BorrowDef>);

pub struct Cxt<'a> {
    pub db: &'a dyn Elaborator,
    scopes: Vec<Scope>,
    env: Env,
    errors: Vec<(Severity, TypeError, RelSpan)>,
    pub mcxt: MetaCxt<'a>,
    expr_borrow: Vec<Borrow>,
    borrows: Vec<BorrowDef>,
    borrows_start: u64,
}
impl Cxt<'_> {
    pub fn new(db: &dyn Elaborator, def_cxt: DefCxt) -> Cxt {
        let mut cxt = Cxt {
            db,
            env: Env::new(Size::zero()),
            scopes: def_cxt.scopes,
            errors: Vec::new(),
            mcxt: MetaCxt::new(db),
            expr_borrow: Vec::new(),
            borrows: Vec::new(),
            borrows_start: def_cxt.n_borrows,
        };
        cxt.record_deps();
        cxt.env = Env::new(cxt.size());
        cxt
    }

    pub fn borrow_checkpoint(&self) -> BorrowCheckpoint {
        BorrowCheckpoint(self.borrows.clone())
    }
    pub fn reset_borrows(&mut self, checkpoint: BorrowCheckpoint) -> BorrowCheckpoint {
        let ret = self.borrow_checkpoint();
        // Keep borrows created after checkpoint so that the Borrow indices line up
        for (i, b) in checkpoint.0.into_iter().enumerate() {
            self.borrows[i] = b;
        }
        ret
    }
    pub fn merge_borrows(&mut self, checkpoint: BorrowCheckpoint) {
        for (i, b) in checkpoint.0.into_iter().enumerate() {
            if let Some(invalid) = self.borrows[i].merge_with(b) {
                Borrow((i as u64 + 1).try_into().unwrap()).invalidate(invalid, self);
            }
        }
    }

    pub fn record_deps(&mut self) {
        let borrow = Borrow::new(self);
        self.expr_borrow.push(borrow)
    }
    pub fn finish_deps(&mut self, span: RelSpan) -> Borrow {
        let borrow = self.expr_borrow.pop().unwrap();
        // If an error occurs here, it's because of an invalid access within the expression
        let access = Access {
            kind: AccessKind::Imm,
            point: AccessPoint::Expr,
            span,
        };
        self.check_deps(borrow, access)
            .map(|()| borrow)
            .unwrap_or_else(|e| {
                self.error(RelSpan::empty(), e);
                borrow
            })
    }
    pub fn add_dep(&mut self, dep: Borrow, access: Access) {
        dep.add_borrow(*self.expr_borrow.last().unwrap(), access, self)
    }
    pub fn check_deps(&self, borrow: Borrow, access: Access) -> Result<(), MoveError> {
        match borrow.def(self) {
            Some(def) => {
                if let Some(BorrowInvalid {
                    skip_borrow: _,
                    base_access,
                    chain_start,
                    chain_end,
                    move_type,
                }) = def.invalid.clone()
                {
                    return Err(AccessError {
                        invalid_access: access,
                        dep_chain_start: chain_start,
                        dep_chain_end: chain_end,
                        dep_access: base_access,
                        move_type,
                    }
                    .into());
                }
            }
            None => {
                return Err(MoveError::InvalidAccess(
                    Doc::start("Cannot access outside local in definition"),
                    access,
                ))
            }
        }
        Ok(())
    }

    pub fn unify(
        &mut self,
        inferred: Val,
        expected: Val,
        reason: CheckReason,
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
        borrow: Option<Borrow>,
        mutable: bool,
    ) {
        let borrow = borrow.unwrap_or_else(|| Borrow::new(self));
        self.scope_mut()
            .unwrap()
            .define_local(name, ty, borrow, mutable);
        self.env.push(value.map(Ok));
    }

    pub fn define(&mut self, name: SName, var: Var<Lvl>, ty: Val) {
        if matches!(var, Var::Local(_, _)) {
            panic!("Call define_local() for local variables!");
        }
        self.scope_mut().unwrap().define(name, var, ty, None, false);
    }

    pub fn def_cxt(&self) -> DefCxt {
        DefCxt {
            scopes: self.scopes.clone(),
            n_borrows: self.borrows_start + self.borrows.len() as u64,
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

    pub fn resolve_self(&self) -> Option<Def> {
        self.scopes.iter().rev().find_map(|x| match x {
            Scope::Namespace(Namespace::Def(def)) => Some(*def),
            _ => None,
        })
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

    fn record_access(&mut self, lvl: Lvl, access: Access) {
        let class = match access.kind {
            AccessKind::Move => CopyClass::Move,
            AccessKind::Mut => CopyClass::Mut,
            AccessKind::Imm | AccessKind::Copy => CopyClass::Copy,
        };
        for i in self.scopes.iter_mut().rev() {
            match i {
                Scope::Local(l) => {
                    if !lvl.in_scope(l.start_size) {
                        break;
                    } else if let Some(captures) = &mut l.captures {
                        let mut found = false;
                        for (l, x) in captures.iter_mut() {
                            if *l == lvl {
                                match x {
                                    (c, _) if *c >= class => (),
                                    _ => *x = (class, access),
                                }
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            captures.push((lvl, (class, access)));
                        }
                    }
                }
                _ => (),
            }
        }
    }

    pub fn push(&mut self) {
        self.scopes
            .push(Scope::Local(LocalScope::new(self.size(), false)));
    }

    pub fn push_capture(&mut self) {
        self.scopes
            .push(Scope::Local(LocalScope::new(self.size(), true)));
    }

    pub fn push_def_scope(&mut self, def: Def) {
        self.scopes.push(Scope::Namespace(Namespace::Def(def)));
    }

    pub fn pop(&mut self) -> Option<Vec<(Lvl, (CopyClass, Access))>> {
        let scope = self.scopes.pop();
        self.env.reset_to_size(self.size());
        scope.and_then(|x| match x {
            Scope::Local(l) => l.captures,
            _ => None,
        })
    }

    pub fn lookup(&self, name: SName) -> Option<VarEntry> {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, x)| x.lookup(i, name, self.db))
    }

    pub fn local_entry(&self, lvl: Lvl) -> VarEntry {
        let (name, scope, idx) = self
            .scopes
            .iter()
            .enumerate()
            .find_map(|(i, x)| match x {
                Scope::Local(x) => x.names.iter().enumerate().find_map(|(j, x)| match &x.var {
                    VarDef::Var(Var::Local(n, l), _) if *l == lvl => Some((*n, i, j)),
                    _ => None,
                }),
                _ => None,
            })
            .unwrap();
        VarEntry::Local {
            name,
            scope,
            var: idx,
        }
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
