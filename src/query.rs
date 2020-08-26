use crate::elaborate::*;
use crate::error::*;
use crate::evaluate::*;
use crate::term::*;
use std::sync::{Arc, Mutex};

macro_rules! intern_id {
    ($name:ident) => {
        #[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        /// This is a handle to the actual object stored in the Salsa database.
        pub struct $name(salsa::InternId);
        impl salsa::InternKey for $name {
            fn from_intern_id(id: salsa::InternId) -> Self {
                Self(id)
            }

            fn as_intern_id(&self) -> salsa::InternId {
                self.0
            }
        }
    };
}

intern_id!(Name);
impl Name {
    pub fn get<T: Interner + ?Sized>(self, db: &T) -> String {
        db.lookup_intern_name(self)
    }
}
intern_id!(DefId);
intern_id!(Cxt);
impl Cxt {
    pub fn size<T: ?Sized + Interner>(self, db: &T) -> Lvl {
        match db.lookup_cxt_entry(self) {
            MaybeEntry::Yes(CxtEntry { size, .. }) => size,
            MaybeEntry::No(_) => Lvl::zero(),
        }
        // let mut cxt = self;
        // let mut l = Lvl::zero();
        // while let Some(CxtEntry { name, info, rest }) = db.lookup_cxt_entry(cxt) {
        //     match info {
        //         NameInfo::Local(_) => l = l.inc(),
        //         _ => (),
        //     }
        //     cxt = rest;
        // }
        // l
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

    pub fn lookup<T: ?Sized + Interner>(self, sym: Name, db: &T) -> Option<NameResult> {
        let mut cxt = self;
        let mut ix = Ix::zero();
        while let MaybeEntry::Yes(CxtEntry {
            name, info, rest, ..
        }) = db.lookup_cxt_entry(cxt)
        {
            match info {
                NameInfo::Def(id) => {
                    if name == sym {
                        return Some(NameResult::Def(id));
                    }
                }
                NameInfo::Local(ty) => {
                    if name == sym {
                        return Some(NameResult::Local(ix, ty));
                    } else {
                        ix = ix.inc()
                    }
                }
            }
            cxt = rest;
        }
        None
    }

    #[must_use]
    pub fn define<T: ?Sized + Interner>(self, name: Name, info: NameInfo, db: &T) -> Cxt {
        let (file, size) = match db.lookup_cxt_entry(self) {
            MaybeEntry::Yes(CxtEntry { file, size, .. }) => (file, size),
            MaybeEntry::No(file) => (file, Lvl::zero()),
        };
        db.cxt_entry(MaybeEntry::Yes(CxtEntry {
            name,
            info,
            file,
            size: size.inc(),
            rest: self,
        }))
    }

    pub fn new<T: ?Sized + Interner>(file: FileId, db: &T) -> Cxt {
        db.cxt_entry(MaybeEntry::No(file))
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum NameResult {
    Def(DefId),
    Local(Ix, VTy),
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum NameInfo {
    Def(DefId),
    Local(VTy),
}

/// One cell of the context linked list.
/// See `Interner::add_def`.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct CxtEntry {
    name: Name,
    info: NameInfo,
    file: FileId,
    size: Lvl,
    rest: Cxt,
}
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum MaybeEntry {
    Yes(CxtEntry),
    No(FileId),
}

#[salsa::query_group(InternerDatabase)]
pub trait Interner: salsa::Database {
    #[salsa::interned]
    fn intern_name(&self, s: String) -> Name;

    #[salsa::interned]
    fn intern_def(&self, def: Arc<PreDef>, cxt: Cxt) -> DefId;

    /// The context is stored as a linked list, but the links are hashmap keys!
    /// This is... pretty slow, but has really good incrementality.
    #[salsa::interned]
    fn cxt_entry(&self, key: MaybeEntry) -> Cxt;
}

pub trait CompilerExt: Interner {
    fn report_error(&self, error: Error);

    fn num_errors(&self) -> usize;

    fn write_errors(&self);
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DefError {
    /// This happens when we try to get the value of a definition that doesn't have one, like a declaration
    NoValue,
    ElabError,
}

#[salsa::query_group(CompilerDatabase)]
pub trait Compiler: CompilerExt + Interner {
    #[salsa::input]
    fn file_source(&self, file: FileId) -> String;

    /// Returns a list of the interned defs
    fn top_level(&self, file: FileId) -> Arc<Vec<DefId>>;

    fn elaborate_def(&self, def: DefId) -> Result<(Arc<Term>, Arc<VTy>), DefError>;

    fn def_type(&self, def: DefId) -> Result<Arc<VTy>, DefError>;
}

fn def_type(db: &dyn Compiler, def: DefId) -> Result<Arc<VTy>, DefError> {
    db.elaborate_def(def).map(|(_, ty)| ty)
}

fn top_level(db: &dyn Compiler, file: FileId) -> Arc<Vec<DefId>> {
    use crate::grammar::DefsParser;

    let source = db.file_source(file);

    let parser = DefsParser::new();
    let cxt = Cxt::new(file, db);
    match parser.parse(db, &source) {
        Ok(v) => Arc::new(
            v.into_iter()
                .map(|def| db.intern_def(Arc::new(def), cxt))
                .collect(),
        ),
        Err(e) => {
            db.report_error(e.to_error(file));
            Arc::new(Vec::new())
        }
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
        self.errors.lock().unwrap().push(error)
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

impl Database {
    pub fn check_all(&self, file: FileId) {
        for def in &*self.top_level(file) {
            self.elaborate_def(*def);
        }
    }
}
