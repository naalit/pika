use std::{num::NonZeroU64, rc::Rc};

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

    fn all_defs(self, db: &(impl Elaborator + ?Sized)) -> Vec<Def> {
        match self {
            Namespace::Global(file) => db
                .all_split_ids(file)
                .into_iter()
                .map(|split| db.def(DefLoc::Root(file, split)))
                .collect(),
            Namespace::Def(def) => db
                .def_type(def)
                .and_then(|x| x.result)
                .map(|x| {
                    x.children
                        .into_iter()
                        .map(|x| db.def(DefLoc::Child(def, x)))
                        .collect()
                })
                .unwrap_or_default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Scope {
    Prelude,
    Trait(Val),
    Namespace(Namespace),
    Local(LocalScope),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalScope {
    size: Size,
    start_size: Size,
    names: Vec<LocalVarDef>,
    captures: Option<(Borrow, Vec<(Lvl, Access)>)>,
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
            Scope::Trait(_) => None,
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

    fn new(size: Size, capture: Option<Borrow>) -> Self {
        LocalScope {
            size,
            start_size: size,
            names: Vec::new(),
            captures: capture.map(|x| (x, Vec::new())),
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
    /// These are borrows that don't borrow this one, but do depend on it by-value - so if this gets invalidated indirectly, they will too
    owned_dependents: HashMap<Borrow, Access>,
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
        self.owned_dependents.extend(other.owned_dependents);
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
pub struct Borrow(NonZeroU64);
impl Borrow {
    pub fn new(cxt: &mut Cxt) -> Borrow {
        cxt.borrows.push(BorrowDef::default());
        Borrow((cxt.borrows.len() as u64).try_into().unwrap())
    }

    fn def_mut<'a>(self, cxt: &'a mut Cxt) -> Option<&'a mut BorrowDef> {
        let idx = self.0.get() - 1;
        cxt.borrows.get_mut(idx as usize)
    }
    fn def<'a>(self, cxt: &'a Cxt) -> Option<&'a BorrowDef> {
        let idx = self.0.get() - 1;
        cxt.borrows.get(idx as usize)
    }

    pub fn mutable_dependencies(self, cxt: &Cxt) -> Vec<(Borrow, Access)> {
        self.def(cxt)
            .map(|d| d.mutable_parents.iter().map(|(&x, &y)| (x, y)).collect())
            .unwrap_or_default()
    }

    fn invalidate(self, invalid: BorrowInvalid, cxt: &mut Cxt) {
        if invalid.skip_borrow == Some(self) {
            return;
        }
        if let Some(def) = self.def_mut(cxt) {
            if def.invalid.is_none() {
                def.invalid = Some(invalid.clone());
                for (i, a) in def
                    .immutable_borrows
                    .iter()
                    .chain(&def.owned_dependents)
                    .chain(&def.mutable_borrows)
                    .map(|(&x, &y)| (x, y))
                    .collect::<Vec<_>>()
                {
                    let mut invalid = invalid.clone();
                    if invalid.chain_start.is_none() {
                        invalid.chain_start = Some(a);
                    } else {
                        invalid.chain_end = Some(a);
                    }
                    i.invalidate(invalid, cxt);
                }
            } else if !def.owned_dependents.is_empty() {
                for (i, a) in def.owned_dependents.clone() {
                    let mut invalid = invalid.clone();
                    if invalid.chain_start.is_none() {
                        invalid.chain_start = Some(a);
                    } else {
                        invalid.chain_end = Some(a);
                    }
                    i.invalidate(invalid, cxt);
                }
            }
        }
    }
    pub fn invalidate_children(self, access: Access, cxt: &mut Cxt) {
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
        // Don't invalidate owned dependents
        self.invalidate_children(access, cxt);
        if let Some(def) = self.def_mut(cxt) {
            if def.invalid.is_none() {
                def.invalid = Some(BorrowInvalid {
                    skip_borrow: None,
                    base_access: access,
                    chain_start: None,
                    chain_end: None,
                    move_type: Some(move_type),
                });
            }
        }
    }

    /// Does not check validity or invalidate old borrows - do that before calling this
    pub fn add_borrow(self, borrow: Borrow, access: Access, cxt: &mut Cxt) {
        if let Some(def) = self.def_mut(cxt) {
            match access.kind {
                Cap::Mut => {
                    def.mutable_borrows.insert(borrow, access);
                    if let Some(def) = borrow.def_mut(cxt) {
                        def.mutable_parents.insert(self, access);
                    }
                }
                Cap::Imm => {
                    def.immutable_borrows.insert(borrow, access);
                }
                Cap::Own => {
                    def.owned_dependents.insert(borrow, access);
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
    ClosureEnv(RelSpan, Option<Name>),
    EscapingParam(SName),
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
            AccessPoint::ClosureEnv(_, Some(name)) => Doc::start(if initial {
                "Captured variable "
            } else {
                "captured variable "
            })
            .chain(name.pretty(db).style(col)),
            AccessPoint::EscapingParam((name, _)) => Doc::start(if initial { "N" } else { "n" })
                .add("on-", ())
                .add("ref", Doc::style_keyword())
                .add(" parameter ", ())
                .chain(name.pretty(db).style(col)),
            AccessPoint::ClosureEnv(_, None) => {
                Doc::start(if initial { "T" } else { "t" }).add("his closure's environment", ())
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
    pub kind: Cap,
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
            Cap::Own => (
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
            _ if matches!(self.dep_access.point, AccessPoint::ClosureEnv(_, _)) => (
                Doc::start("Cannot return value that borrows mutable ").chain(name0(false, false)),
                name0(true, false).add(
                    " could be mutated by another call to this closure after it is returned",
                    (),
                ),
                false,
            ),
            _ if matches!(self.dep_access.point, AccessPoint::EscapingParam(_)) => (
                Doc::start("Cannot return value that borrows mutable ").chain(name0(false, false)),
                name0(true, false)
                    .add(" is mutable and must be annotated with ", ())
                    .add("ref", Doc::style_keyword())
                    .add(" in order to escape the function", ()),
                false,
            ),
            _ if self
                .dep_chain_start
                .map_or(self.invalid_access.kind == Cap::Mut, |x| x.kind == Cap::Mut) =>
            {
                (
                    name0(true, true).add(" cannot be accessed while mutably borrowed", ()),
                    Doc::start("Mutable borrow later used here"),
                    true,
                )
            }
            Cap::Mut => (
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
            let mutable = access.kind == Cap::Mut;
            secondary.push(Label {
                span: access.span,
                color: Some(Doc::COLOR3),
                message: name0(true, swap) // TODO should this use COLOR3?
                    .add(" was", ())
                    .add(if mutable { " mutably" } else { "" }, ())
                    .add(" borrowed here", ()),
            });
        }
        match self.dep_access.point {
            AccessPoint::ClosureEnv(span, _) => {
                if span != self.invalid_access.span
                    && self.dep_chain_start.map_or(true, |x| x.span != span)
                {
                    secondary.push(Label {
                        span,
                        color: Some(Doc::COLOR4),
                        message: name0(true, swap).add(
                            " could be mutated here when the closure is called again",
                            (),
                        ),
                    })
                }
            }
            _ => (),
        }
        if secondary.len() < 3 {
            if let Some(access) = self.dep_chain_end {
                let mutable = self.dep_chain_start.unwrap().kind == Cap::Mut;
                let span = match self.dep_access.point {
                    AccessPoint::ClosureEnv(span, _) => span,
                    _ => access.span,
                };
                if self.dep_chain_start.map_or(true, |x| span != x.span) {
                    secondary.push(Label {
                        span,
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
            }
        }

        let note = if self.dep_access.kind == Cap::Own {
            self.move_type.as_ref().map(|ty| {
                Doc::start("Move occurs because ")
                    .chain(name0(false, swap))
                    .add(" has type '", ())
                    .chain(ty.pretty(db))
                    .add("' which is mutable", ())
            })
        } else if let AccessPoint::ClosureEnv(_, _) = self.dep_access.point {
            Some(
                Doc::start("Closure could be called more than once since it's a '")
                    .add("mut", Doc::style_keyword())
                    .add("->' closure, not an owned '->' closure", ()),
            )
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
    InvalidMove(Doc, Option<Name>, Box<Expr>),
    InvalidBorrow(Doc, Name),
    // If the Cap is None, it means a pi type
    FunAccess(Access, Option<Cap>, Option<(Expr, CheckReason)>),
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
                .map_or(Val::Error, |x| x.ty),
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

    pub fn access(&self, kind: Cap) -> Access {
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

    // TODO do we need the type for anything? if not we should combine these into `try_access(cap: Cap)`
    pub fn try_move(&self, ty: Expr, cxt: &mut Cxt) -> Result<(), MoveError> {
        if let Some(borrow) = self.borrow(cxt) {
            cxt.check_deps(borrow, self.access(Cap::Own))?;
        }
        match self {
            VarEntry::Local { scope, var, .. } => match &mut cxt.scopes[*scope] {
                Scope::Local(l) => {
                    let entry = &mut l.names[*var];
                    let lvl = entry.var.as_var().unwrap().as_local();
                    let access = self.access(Cap::Own);
                    let borrow = entry.borrow.unwrap();
                    borrow.invalidate_self(access, Rc::new(ty), cxt);
                    if let Some(lvl) = lvl {
                        cxt.record_access(lvl, access, borrow);
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
                Some(name.0),
                Box::new(ty),
            )),
            VarEntry::Other { var, name } => Err(MoveError::InvalidMove(
                Doc::start("Cannot move out of ").debug(var),
                Some(name.0),
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
                    if let Some(borrow) = entry.borrow {
                        let access = self.access(if mutable { Cap::Mut } else { Cap::Imm });
                        cxt.check_deps(borrow, access)?;

                        let lvl = entry.var.as_var().unwrap().as_local();
                        if mutable {
                            borrow.invalidate_children(access, cxt);
                        } else {
                            borrow.invalidate_mutable(access, cxt);
                        }
                        if let Some(lvl) = lvl {
                            cxt.record_access(lvl, access, borrow);
                        }
                    }
                    Ok(())
                }
                _ => unreachable!(),
            },
            // It's fine to borrow definitions/builtins immutably, they can't ever be mutated
            VarEntry::Other { .. } if !mutable => Ok(()),
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
            kind: Cap::Imm,
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
    // TODO do we still need this?
    pub fn finish_closure_env(&mut self, dep: Borrow, cap: Cap, span: RelSpan) -> Borrow {
        let new_borrow = Borrow::new(self);
        match dep.def(self) {
            Some(def) => {
                let def = def.clone();
                if cap == Cap::Mut {
                    for i in &def.mutable_borrows {
                        let access = Access {
                            kind: Cap::Mut,
                            span,
                            point: AccessPoint::ClosureEnv(
                                i.1.span,
                                match i.1.point {
                                    AccessPoint::Name(n) => Some(n),
                                    _ => None,
                                },
                            ),
                        };
                        i.0.invalidate_children(access, self);
                    }
                }
                for (&i, &a) in def
                    .immutable_borrows
                    .iter()
                    .chain(&def.owned_dependents)
                    .chain(&def.mutable_borrows)
                {
                    i.add_borrow(new_borrow, a, self);
                }
            }
            None => (),
        }
        new_borrow
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
        }
    }

    pub fn new_meta(&mut self, bounds: MetaBounds, span: RelSpan, source: MetaSource) -> Expr {
        self.mcxt
            .new_meta(self.locals(), self.size(), bounds, span, source)
    }

    pub fn emit_errors(mut self) -> Vec<Error> {
        let errors = self.mcxt.error_unsolved();
        self.errors
            .into_iter()
            .map(|(severity, x, span)| x.to_error(severity, span, self.db))
            .chain(errors)
            .collect()
    }

    pub fn size(&self) -> Size {
        self.scope().map_or(Size::zero(), |x| x.size)
    }

    pub fn resolve_self(&self, span: RelSpan) -> Option<Expr> {
        self.scopes.iter().rev().find_map(|x| match x {
            Scope::Namespace(Namespace::Def(def)) => Some(Expr::var(Var::Def(
                (self.db.name("Self".into()), span),
                *def,
            ))),
            Scope::Trait(val) => Some(val.clone().quote(self.size(), None)),
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

    fn record_access(&mut self, lvl: Lvl, access: Access, borrow: Borrow) {
        let mut deps = Vec::new();
        for i in self.scopes.iter_mut().rev() {
            match i {
                Scope::Local(l) => {
                    if !lvl.in_scope(l.start_size) {
                        break;
                    } else if let Some((b, captures)) = &mut l.captures {
                        let mut found = false;
                        for (l, x) in captures.iter_mut() {
                            if *l == lvl {
                                if access.kind > x.kind {
                                    *x = access;
                                }
                                found = true;
                                break;
                            }
                        }
                        if !found {
                            captures.push((lvl, access));
                        }
                        deps.push(*b);
                    }
                }
                _ => (),
            }
        }
        for b in deps {
            b.add_borrow(borrow, access, self);
        }
    }

    pub fn push(&mut self) {
        self.scopes
            .push(Scope::Local(LocalScope::new(self.size(), None)));
    }

    pub fn mark_top_scope_capture(&mut self) {
        let borrow = Borrow::new(self);
        assert!(
            self.scope_mut()
                .unwrap()
                .captures
                .replace((borrow, Vec::new()))
                .is_none(),
            "Cannot mark_capture() a scope that is already capture"
        );
    }

    pub fn push_def_scope(&mut self, def: Def) {
        self.scopes.push(Scope::Namespace(Namespace::Def(def)));
    }

    pub fn push_trait_scope(&mut self) {
        self.scopes.push(Scope::Trait(Val::var(Var::Local(
            (self.db.name("Self".into()), RelSpan::empty()),
            Size::zero().next_lvl(),
        ))));
    }

    pub fn push_trait_impl_scope(&mut self, self_arg: Val) {
        self.scopes.push(Scope::Trait(self_arg));
    }

    pub fn pop(&mut self) -> Option<(Borrow, Vec<(Lvl, Access)>)> {
        let new_size = self
            .scopes
            .iter()
            .rev()
            .skip(1)
            .find_map(|x| match x {
                Scope::Local(l) => Some(l.size),
                _ => None,
            })
            .unwrap_or(self.size());
        if matches!(self.scopes.last(), Some(Scope::Local(_))) {
            self.resolve_impls(new_size);
        }

        let scope = self.scopes.pop();
        self.env.reset_to_size(self.size());
        scope.and_then(|x| match x {
            Scope::Local(l) => l.captures,
            _ => None,
        })
    }

    fn resolve_impls(&mut self, new_size: Size) {
        let metas = self.mcxt.needed_impls(new_size);
        if !metas.is_empty() {
            let locals: Vec<_> = self
                .locals()
                .into_iter()
                .map(|(n, l)| (n, l, self.local_ty(l)))
                .collect();
            for (meta, msize, mspan) in metas {
                let mty = self.mcxt.meta_ty(meta).unwrap();
                let trait_def = match mty.uncap_ty() {
                    Val::Neutral(neutral) => match neutral.head() {
                        Head::Var(Var::Def(_, trait_def)) => trait_def,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };

                // Start by searching locals
                let mut solutions = Vec::new();
                for (n, l, lty) in locals.iter().take(msize.as_u32() as usize) {
                    // on this insert_metas and the next one, we need to save a checkpoint of the mcxt
                    // bc if unification fails we could get random metas lying around that will go unsolved
                    let cp = self.mcxt.checkpoint();
                    let (lval, lty) = Expr::var(Var::Local((*n, mspan), l.idx(self.size())))
                        .insert_metas(lty.clone(), None, mspan, self);
                    match lty.uncap_ty() {
                        Val::Neutral(n2) if matches!(n2.head(), Head::Var(Var::Def(_, d)) if d ==  trait_def) => {
                            match self.mcxt.unify(
                                lty.clone(),
                                mty.clone(),
                                msize,
                                self.env(),
                                CheckReason::MustMatch(mspan),
                            ) {
                                Ok(()) => {
                                    solutions.push(lval.eval(&mut self.env()));
                                }
                                Err(_) => self.mcxt.reset_to(cp),
                            }
                        }
                        _ => self.mcxt.reset_to(cp),
                    }
                }

                // Now search impls in scope
                if solutions.is_empty() {
                    let impls: Vec<_> = self
                        .scopes
                        .iter()
                        .rev()
                        .flat_map(|x| match x {
                            Scope::Local(l) => l
                                .names
                                .iter()
                                .filter_map(|x| match x.var {
                                    VarDef::Var(_, _) => None,
                                    VarDef::Def(d) => Some(d),
                                })
                                .collect(),
                            Scope::Namespace(n) => n.all_defs(self.db),
                            _ => vec![],
                        })
                        .filter(|x| {
                            self.db
                                .def_type(*x)
                                .and_then(|x| x.result)
                                .map_or(false, |x| x.is_impl)
                        })
                        .collect();
                    for idef in impls {
                        let cp = self.mcxt.checkpoint();
                        let ity = self.db.def_type(idef).unwrap().result.unwrap().ty;
                        let (ival, ity) =
                            Expr::var(Var::Def((self.db.name("_".into()), mspan), idef))
                                .insert_metas(ity, None, mspan, self);
                        match ity.uncap_ty() {
                            Val::Neutral(n2) if matches!(n2.head(), Head::Var(Var::Def(_, d)) if d ==  trait_def) => {
                                match self.mcxt.unify(
                                    ity.clone(),
                                    mty.clone(),
                                    msize,
                                    self.env(),
                                    CheckReason::MustMatch(mspan),
                                ) {
                                    Ok(()) => {
                                        solutions.push(ival.eval(&mut self.env()));
                                    }
                                    Err(_) => self.mcxt.reset_to(cp),
                                }
                            }
                            _ => self.mcxt.reset_to(cp),
                        }
                    }
                }

                match solutions.len() {
                    0 => {
                        self.error(
                            mspan,
                            TypeError::Other(
                                Doc::start("Could not find impl for '")
                                    .chain(mty.quote(msize, Some(&self.mcxt)).pretty(self.db))
                                    .add("' in this scope", ()),
                            ),
                        );
                        self.mcxt.mark_meta_error(meta);
                    }
                    1 => {
                        let spine = locals
                            .iter()
                            // We might have defined more locals since the meta intro, so make sure we have the right spine length
                            .take(msize.as_u32() as usize)
                            .fold(None, |rest, &(n, l, _)| {
                                let x = Expr::var(Var::Local((n, RelSpan::empty()), l.idx(msize)));
                                match rest {
                                    // TODO do we ever need these types?
                                    Some(rest) => Some(Expr::Pair(
                                        Box::new(x),
                                        Box::new(rest),
                                        Box::new(Expr::Error),
                                    )),
                                    None => Some(x),
                                }
                            })
                            .unwrap()
                            .eval(&mut Env::new(msize));
                        if let Err(e) = self.mcxt.solve(
                            msize,
                            meta,
                            vec![Elim::App(Expl, spine)],
                            solutions.pop().unwrap(),
                            true,
                        ) {
                            self.error(
                                mspan,
                                Doc::start("Error resolving impl for '")
                                    .chain(mty.quote(msize, Some(&self.mcxt)).pretty(self.db))
                                    .add(": ", ())
                                    .chain(e.pretty(self.db)),
                            );
                        }
                    }
                    _ => {
                        // TODO incorporate spans of candidates
                        self.error(
                            mspan,
                            Doc::start("Multiple ambiguous impls for '")
                                .chain(mty.quote(msize, Some(&self.mcxt)).pretty(self.db))
                                .add("'", ()),
                        );
                        self.mcxt.mark_meta_error(meta);
                    }
                }
            }
        }
    }

    pub fn lookup(&self, name: SName) -> Option<VarEntry> {
        self.scopes
            .iter()
            .enumerate()
            .rev()
            .find_map(|(i, x)| x.lookup(i, name, self.db))
    }

    pub fn all_traits(&self) -> impl Iterator<Item = Def> + '_ {
        self.scopes
            .iter()
            .rev()
            .flat_map(|x| match x {
                Scope::Local(l) => l
                    .names
                    .iter()
                    .filter_map(|x| match x.var {
                        VarDef::Var(_, _) => None,
                        VarDef::Def(d) => Some(d),
                    })
                    .collect(),
                Scope::Namespace(n) => n.all_defs(self.db),
                _ => vec![],
            })
            .filter(|x| {
                self.db
                    .def_type(*x)
                    .and_then(|x| x.result)
                    .map_or(false, |x| x.is_trait)
            })
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

    pub fn has_error(&self) -> bool {
        self.errors.iter().any(|(s, _, _)| *s == Severity::Error)
    }

    pub fn error(&mut self, span: RelSpan, error: impl Into<TypeError>) {
        self.errors.push((Severity::Error, error.into(), span));
    }

    pub fn warning(&mut self, span: RelSpan, error: impl Into<TypeError>) {
        self.errors.push((Severity::Warning, error.into(), span));
    }
}
