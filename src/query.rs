use crate::elaborate::*;
use crate::error::*;
use crate::term::*;
use std::sync::{Arc, Mutex};

macro_rules! intern_id {
    ($name:ident, $doc:expr) => {
        #[doc=$doc]
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        pub struct $name(salsa::InternId);
        impl $name {
            /// Returns the underlying number identifying the object, for debugging purposes
            pub fn num(self) -> u32 {
                self.0.as_u32()
            }
        }
        impl salsa::InternKey for $name {
            fn from_intern_id(id: salsa::InternId) -> Self {
                Self(id)
            }

            fn as_intern_id(&self) -> salsa::InternId {
                self.0
            }
        }
    };
    ($name:ident) => {
        intern_id!(
            $name,
            "This is a handle to the actual object stored in the Salsa database."
        )
    };
}

intern_id!(Name, "An identifier, represented as an interned string.");
impl Name {
    pub fn get<T: Interner + ?Sized>(self, db: &T) -> String {
        db.lookup_intern_name(self)
    }
}
intern_id!(
    DefId,
    "A reference to a definition and the context, which are interned in the Salsa database."
);
intern_id!(
    PreDefId,
    r#"A reference to a definition, but without context.
This is needed for (mutually) recursive definitions, where context for one definition requires the others."#
);
intern_id!(
    ScopeId,
    "A reference to a scope with members, for a datatype's associated module or a structure."
);
intern_id!(
    TypeId,
    "A reference to a datatype and its constructors, but not its associated module."
);
intern_id!(
    Cxt,
    r#"The context for resolving names, represented as a linked list of definitions, with the links stored in Salsa.
This is slower than a hashmap or flat array, but it has better incrementality."#
);
impl Cxt {
    pub fn size<T: ?Sized + Interner>(self, db: &T) -> Size {
        match db.lookup_cxt_entry(self) {
            MaybeEntry::Yes(CxtEntry { size, .. }) => size,
            MaybeEntry::No(_) => Size::zero(),
        }
    }

    pub fn env<T: ?Sized + Interner>(self, db: &T) -> Env {
        Env::new(self.size(db))
    }

    pub fn file<T: ?Sized + Interner>(self, db: &T) -> FileId {
        match db.lookup_cxt_entry(self) {
            MaybeEntry::Yes(CxtEntry { file, .. }) => file,
            MaybeEntry::No(file) => file,
        }
    }

    pub fn lookup(self, sym: Name, db: &dyn Compiler) -> Result<(Var<Ix>, VTy), DefError> {
        let mut cxt = self;
        let mut ix = Ix::zero();
        while let MaybeEntry::Yes(CxtEntry {
            name, info, rest, ..
        }) = db.lookup_cxt_entry(cxt)
        {
            match info {
                NameInfo::Def(id) => {
                    if name == sym {
                        return Ok((Var::Top(id), (*db.def_type(id)?).clone()));
                    }
                }
                NameInfo::Error => {
                    if name == sym {
                        return Err(DefError::ElabError);
                    }
                }
                NameInfo::Local(ty) => {
                    if name == sym {
                        return Ok((Var::Local(ix), ty));
                    } else {
                        ix = ix.inc()
                    }
                }
                NameInfo::Rec(id, ty) => {
                    if name == sym {
                        return Ok((Var::Rec(id), ty));
                    }
                }
                NameInfo::Other(v, ty) => {
                    if name == sym {
                        return Ok((v, ty));
                    }
                }
            }
            cxt = rest;
        }
        Err(DefError::NoValue)
    }

    pub fn lookup_rec(self, rec: PreDefId, db: &dyn Compiler) -> Option<(Var<Lvl>, Option<Val>)> {
        let mut cxt = self;
        while let MaybeEntry::Yes(CxtEntry { info, rest, .. }) = db.lookup_cxt_entry(cxt) {
            match info {
                NameInfo::Def(id) => {
                    if db.lookup_intern_def(id).0 == rec {
                        return Some((Var::Top(id), None));
                    }
                }
                NameInfo::Error => (),
                NameInfo::Rec(id, _) => {
                    if id == rec {
                        return None;
                    }
                }
                NameInfo::Other(Var::Type(id, sc), ty) => {
                    if db.lookup_intern_def(id).0 == rec {
                        return Some((Var::Type(id, sc), Some(ty)));
                    }
                }
                NameInfo::Local(_) | NameInfo::Other(_, _) => (),
            }
            cxt = rest;
        }
        None
    }

    #[must_use]
    pub fn define<T: ?Sized + Interner>(self, name: Name, info: NameInfo, db: &T) -> Cxt {
        let (file, size) = match db.lookup_cxt_entry(self) {
            MaybeEntry::Yes(CxtEntry { file, size, .. }) => (file, size),
            MaybeEntry::No(file) => (file, Size::zero()),
        };
        let next_size = match &info {
            NameInfo::Local(_) => size.inc(),
            _ => size,
        };
        db.cxt_entry(MaybeEntry::Yes(CxtEntry {
            name,
            info,
            file,
            size: next_size,
            rest: self,
        }))
    }

    pub fn new<T: ?Sized + Interner>(file: FileId, db: &T) -> Cxt {
        let cxt = db.cxt_entry(MaybeEntry::No(file));
        crate::builtins::define_builtins(cxt, db)
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
pub enum RecSolution {
    Global(PreDefId, u16, FileSpan, Term, MetaSource),
    ParentLocal(DefId, u16, FileSpan, Term),
}
impl RecSolution {
    pub fn id(&self) -> Option<PreDefId> {
        match self {
            RecSolution::Global(id, _, _, _, _) => Some(*id),
            _ => None,
        }
    }

    pub fn num(&self) -> u16 {
        match self {
            RecSolution::Global(_, n, _, _, _) | RecSolution::ParentLocal(_, n, _, _) => *n,
        }
    }

    pub fn term(&self) -> &Term {
        match self {
            RecSolution::Global(_, _, _, v, _) | RecSolution::ParentLocal(_, _, _, v) => v,
        }
    }

    pub fn span(&self) -> FileSpan {
        match self {
            RecSolution::Global(_, _, s, _, _) | RecSolution::ParentLocal(_, _, s, _) => *s,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum NameInfo {
    Def(DefId),
    Local(VTy),
    Rec(PreDefId, VTy),
    Other(Var<Ix>, VTy),
    Error,
}

/// One cell of the context linked list.
/// See `Interner::cxt_entry`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CxtEntry {
    pub name: Name,
    pub info: NameInfo,
    pub file: FileId,
    pub size: Size,
    pub rest: Cxt,
}
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum MaybeEntry {
    Yes(CxtEntry),
    No(FileId),
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct ElabInfo {
    pub term: Option<Arc<Term>>,
    pub typ: Arc<VTy>,
    pub solved_globals: Arc<Vec<RecSolution>>,
    /// Only used for definitions in the associated namespace of a datatype
    pub children: Arc<Vec<DefId>>,
    /// Used for definitions in do blocks with open effect scopes
    pub effects: Arc<Vec<Val>>,
}

#[salsa::query_group(InternerDatabase)]
pub trait Interner: salsa::Database {
    #[salsa::interned]
    fn intern_name(&self, s: String) -> Name;

    #[salsa::interned]
    fn intern_predef(&self, def: Arc<PreDefAn>) -> PreDefId;

    #[salsa::interned]
    fn intern_def(&self, def: PreDefId, state: CxtState) -> DefId;

    #[salsa::interned]
    fn intern_scope(&self, scope: Arc<Vec<(Name, DefId)>>) -> ScopeId;

    #[salsa::interned]
    fn intern_type(&self, constructors: Arc<Vec<(Name, DefId)>>) -> TypeId;

    /// The context is stored as a linked list, but the links are hashmap keys!
    /// This is... pretty slow, but has really good incrementality.
    #[salsa::interned]
    fn cxt_entry(&self, key: MaybeEntry) -> Cxt;
}

pub trait CompilerExt: Interner {
    fn report_error(&self, error: Error);
    fn maybe_report_error(&self, error: Option<Error>) {
        if let Some(error) = error {
            self.report_error(error)
        }
    }

    fn num_errors(&self) -> usize;

    fn write_errors(&self);
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DefError {
    /// This happens when we can't find a variable, or we try to get the value of a definition that doesn't have one, like a declaration.
    NoValue,
    ElabError,
}

#[salsa::query_group(CompilerDatabase)]
pub trait Compiler: CompilerExt + Interner {
    #[salsa::input]
    fn file_source(&self, file: FileId) -> String;

    #[salsa::input]
    fn input_files(&self) -> Vec<FileId>;

    fn parsed(&self, file: FileId) -> Option<Arc<Vec<PreDefAn>>>;

    fn file_type(&self, file: FileId) -> Option<Arc<Val>>;

    /// Returns a list of the interned defs
    fn top_level(&self, file: FileId) -> Arc<Vec<DefId>>;

    fn elaborate_def(&self, def: DefId) -> Result<ElabInfo, DefError>;

    fn def_type(&self, def: DefId) -> Result<Arc<VTy>, DefError>;

    fn check_all(&self) -> Vec<RecSolution>;
}

fn def_type(db: &dyn Compiler, def: DefId) -> Result<Arc<VTy>, DefError> {
    db.elaborate_def(def).map(|ElabInfo { typ, .. }| typ)
}

fn parsed(db: &dyn Compiler, file: FileId) -> Option<Arc<Vec<PreDefAn>>> {
    use crate::parser::Parser;

    let source = db.file_source(file);
    let mut parser = Parser::new(db, crate::lexer::Lexer::new(&source));
    match parser.defs() {
        Ok(v) => Some(Arc::new(v)),
        Err(e) => {
            db.report_error(e.into_error(file));
            None
        }
    }
}

fn file_type(db: &dyn Compiler, file: FileId) -> Option<Arc<Val>> {
    let mut cxt = Cxt::new(file, db);
    let v = db.parsed(file)?;
    let mut rv = Vec::new();
    for d in &*v {
        // The DefId doesn't actually matter
        let id = db.intern_predef(Arc::new(d.clone()));
        let d = db.lookup_intern_predef(id);
        match d.given_type(id, cxt, db) {
            Some(ty) => {
                let id = db.intern_def(id, CxtState::new(cxt, db));
                rv.push((id, d.name().unwrap(), ty))
            }
            None => cxt = cxt.define(d.name().unwrap(), NameInfo::Error, db),
        }
    }
    Some(Arc::new(Val::Struct(StructKind::Sig, rv)))
}

fn top_level(db: &dyn Compiler, file: FileId) -> Arc<Vec<DefId>> {
    let mut cxt = Cxt::new(file, db);

    for other_file in db.input_files() {
        if other_file != file {
            let name = {
                use std::path::Path;
                let files = crate::error::FILES.read().unwrap();
                let path: &Path = files.get(other_file).unwrap().name().as_ref();
                path.file_stem().unwrap().to_str().unwrap().to_owned()
            };
            let name = db.intern_name(name);
            let info = match db.file_type(other_file) {
                Some(ty) => NameInfo::Other(Var::File(other_file), Val::Arc(ty)),
                None => NameInfo::Error,
            };
            cxt = cxt.define(name, info, db);
        }
    }

    let state = CxtState::new(cxt, db);
    match db.parsed(file) {
        Some(v) => Arc::new(InternBlock::simple((*v).clone(), state).intern(db)),
        None => Arc::new(Vec::new()),
    }
}

pub struct InternBlock {
    block: Vec<(PreDefAn, Option<(DefId, Ty)>)>,
    state: CxtState,
}
impl InternBlock {
    pub fn new(block: Vec<(PreDefAn, Option<(DefId, Ty)>)>, state: CxtState) -> Self {
        InternBlock { block, state }
    }

    pub fn simple(block: impl IntoIterator<Item = PreDefAn>, state: CxtState) -> Self {
        Self::new(block.into_iter().map(|x| (x, None)).collect(), state)
    }

    pub fn with_cxt(mut self, cxt: Cxt) -> Self {
        self.state.cxt = cxt;
        self
    }

    pub fn intern_tys(&self, db: &dyn Compiler, rv: &mut Vec<(Name, DefId)>) {
        let mut state = self.state.clone();

        for (def, _) in &self.block {
            let span = def.span();
            let name = def.name();
            let def = Arc::new(def.clone());
            let id = db.intern_predef(def.clone());
            if let Some(name) = name {
                if let Some(ty) = def.given_type(id, state.cxt, db) {
                    state.define(name, NameInfo::Rec(id, ty.clone()), db);
                    let def = db.intern_def(
                        db.intern_predef(Arc::new(
                            PreDef::Rec(Spanned::new(name, span), id, ty).into(),
                        )),
                        state.clone(),
                    );
                    rv.push((name, def));
                } else {
                    state.define(name, NameInfo::Error, db);
                }
            }
        }
    }

    pub fn intern(self, db: &dyn Compiler) -> Vec<DefId> {
        let InternBlock { block, mut state } = self;
        let mut rv = Vec::new();
        // This stores unordered definitions (types and functions) between local variables
        let mut temp = Vec::new();
        for (def, old_id) in block {
            if !def.ordered() {
                let name = def.name();
                let def = Arc::new(def);
                let id = db.intern_predef(def.clone());
                if let Some(name) = name {
                    if let Some(ty) = def.given_type(id, state.cxt, db) {
                        state.define(name, NameInfo::Rec(id, ty), db);
                    } else {
                        state.define(name, NameInfo::Error, db);
                    }
                }
                temp.push((name, id, old_id));
            } else {
                // Process `temp` first
                for (name, pre, old_id) in temp.drain(0..) {
                    let id = db.intern_def(pre, state.clone());
                    if let Some(name) = name {
                        // Define it for real now
                        state.define(name, NameInfo::Def(id), db);
                    }
                    rv.push(id);
                    if let Some((old_id, ty)) = old_id {
                        state
                            .local_defs
                            .push((old_id, Term::Var(Var::Top(id), Box::new(ty))));
                    }
                }

                // Then add this one
                let name = def.name();
                let pre = db.intern_predef(Arc::new(def));
                let id = db.intern_def(pre, state.clone());
                if let Some(name) = name {
                    state.define(name, NameInfo::Def(id), db);
                }
                rv.push(id);
                if let Some((old_id, ty)) = old_id {
                    state
                        .local_defs
                        .push((old_id, Term::Var(Var::Top(id), Box::new(ty))));
                }
            }
        }
        // If anything is left in `temp`, clear it out
        for (name, pre, old_id) in temp {
            let id = db.intern_def(pre, state.clone());
            if let Some(name) = name {
                // Define it for real now
                state.define(name, NameInfo::Def(id), db);
            }
            rv.push(id);
            if let Some((old_id, ty)) = old_id {
                state
                    .local_defs
                    .push((old_id, Term::Var(Var::Top(id), Box::new(ty))));
            }
        }
        rv
    }
}

#[salsa::database(InternerDatabase, CompilerDatabase)]
#[derive(Default)]
pub struct Database {
    storage: salsa::Storage<Self>,
    errors: Mutex<Vec<Error>>,
}

impl salsa::Database for Database {}

impl CompilerExt for Database {
    fn report_error(&self, error: Error) {
        self.errors.lock().unwrap().push(error);

        use salsa::Database;
        // Make sure whatever query reported an error runs again next time
        // We need it to report the error again even if nothing changed
        self.salsa_runtime().report_untracked_read();
    }

    fn num_errors(&self) -> usize {
        self.errors.lock().unwrap().len()
    }

    fn write_errors(&self) {
        for err in self.errors.lock().unwrap().drain(0..) {
            err.write().unwrap();
        }
    }
}

fn check_all(db: &dyn Compiler) -> Vec<RecSolution> {
    use crate::pretty::Doc;

    let mut mcxt = MCxt::empty_universal(db);
    for file in db.input_files() {
        // Get meta solutions from each elaborate_def() and make sure they match
        for def in &*db.top_level(file) {
            // They already reported any errors to the database, so we ignore them here
            if let Ok(info) = db.elaborate_def(*def) {
                let info: ElabInfo = info;
                for i in &*info.solved_globals {
                    match i {
                        RecSolution::Global(id, m, span, term, source) => {
                            if let Some(term2) = mcxt.get_meta(Meta::Global(*id, *m, *source)) {
                                let val = term.clone().evaluate(&mcxt.env(), &mcxt);
                                let val2 = term2.clone().evaluate(&mcxt.env(), &mcxt);
                                if !crate::elaborate::unify(
                                    val, val2, mcxt.size, span.span, &mut mcxt,
                                )
                                .unwrap_or(false)
                                {
                                    let span2 =
                                        mcxt.meta_span(Meta::Global(*id, *m, *source)).unwrap();
                                    db.report_error(
                                        Error::new(
                                            span.file,
                                            Doc::start("Could not match types: ")
                                                .chain(source.pretty(db))
                                                .add(" inferred as type ")
                                                .chain(
                                                    term.pretty(db, &mut Names::new(mcxt.cxt, db)),
                                                )
                                                .add(" but previously found to be type ")
                                                .chain(
                                                    term2.pretty(db, &mut Names::new(mcxt.cxt, db)),
                                                ),
                                            span.span,
                                            "type inferred here",
                                        )
                                        .with_label(
                                            span2.file,
                                            span2.span,
                                            "previous type found here",
                                        ),
                                    );
                                }
                            } else {
                                mcxt.solved_globals.push(i.clone());
                            }
                        }
                        RecSolution::ParentLocal(_, _, _, _) => (),
                    }
                }
            }
        }
    }

    mcxt.solved_globals
}
