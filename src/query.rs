use crate::backend::{
    low::{LCtx, Ty},
    LowDef, LowMod,
};
use crate::bicheck::*;
use crate::binding::*;
use crate::common::{Builtins, Doc, FileId, HasBindings, HasDatabase, Pretty, SPretty, Style};
use crate::elab::*;
use crate::error::*;
use crate::grammar::*;
use crate::lexer::Lexer;
use crate::term::*;
use std::cell::Cell;
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::RwLock;

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub enum ScopeId {
    File(FileId),
    /// Structs are always inside of another scope
    Struct(StructId, Box<ScopeId>),
}
impl ScopeId {
    /// There's always a file down there somewhere
    pub fn file(&self) -> FileId {
        match self {
            ScopeId::File(f) => *f,
            ScopeId::Struct(_, parent) => parent.file(),
        }
    }

    /// Inline the members of this scope into a StructInline
    pub fn inline(&self, db: &impl HasDatabase) -> Elab {
        let mut cln = Cloner::new(db);
        let v = db
            .database()
            .symbols(self.clone())
            .iter()
            .filter_map(|s| Some((**s, db.database().elab(self.clone(), **s)?.cloned(&mut cln))))
            .collect();
        Elab::StructInline(v)
    }
}

/// Since queries can't access the database directly, this defines the interface they can use for accessing it
pub trait MainExt: HasBindings {
    fn builtins(&self) -> Builtins;
    fn reset(&self);

    fn has_errors(&self) -> bool;

    /// Report an error to the user
    /// After calling this, queries should attempt to recover as much as possible and continue on
    fn error(&self, e: Error);

    /// Add a module to the struct table
    fn add_mod(&self, id: StructId, file: FileId, defs: &[(Spanned<Sym>, STerm)]);

    /// Get a handle to the struct table
    fn struct_defs(&self, file: FileId, id: StructId) -> Option<Arc<Vec<Def>>>;
}

#[salsa::query_group(MainStorage)]
pub trait MainGroup: MainExt + salsa::Database {
    #[salsa::input]
    fn source(&self, file: FileId) -> Arc<String>;

    #[salsa::input]
    fn options(&self) -> crate::options::Options;

    /// Lists all the definitions in this immediate scope (doesn't include parent scopes)
    fn defs(&self, scope: ScopeId) -> Arc<Vec<Def>>;

    /// Lists all the symbols defined in this immediate scope (doesn't include parent scopes)
    fn symbols(&self, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>>;

    /// Gets the raw term for a definition in this or a parent scope
    fn term(&self, scope: ScopeId, s: Sym) -> Option<Arc<STerm>>;

    /// Gets a definition, type-checked and elaborated
    fn elab(&self, scope: ScopeId, s: Sym) -> Option<Arc<Elab>>;

    /// If the given definition exists, get the name it would be given in code generation
    fn mangle(&self, scope: ScopeId, s: Sym) -> Option<String>;

    fn low_def(&self, scope: ScopeId, s: Sym) -> Option<LowDef>;

    fn low_mod(&self, file: FileId) -> LowMod;

    /// Returns all scopes in this entire file, including the file scope, in order of definition with the file last
    fn child_scopes(&self, file: FileId) -> Arc<Vec<ScopeId>>;
}

fn child_scopes(db: &dyn MainGroup, file: FileId) -> Arc<Vec<ScopeId>> {
    fn add_term(t: &Term, db: &dyn MainGroup, v: &mut Vec<ScopeId>, scope: ScopeId) {
        match t {
            // This is only used for lowering, and data types aren't lowered
            Term::Data(_, _, _, _) => (),
            Term::Struct(s, _) => add_scope(db, v, ScopeId::Struct(*s, Box::new(scope))),
            Term::App(a, b) | Term::Pair(a, b) | Term::The(a, b) => {
                add_term(a, db, v, scope.clone());
                add_term(b, db, v, scope);
            }
            Term::Binder(_, Some(x)) | Term::Project(x, _) | Term::Raise(x) | Term::Catch(x) => {
                add_term(x, db, v, scope)
            }
            Term::Block(t) => t.iter().for_each(|x| match x {
                Statement::Expr(x) | Statement::Def(Def(_, x)) => add_term(x, db, v, scope.clone()),
            }),
            Term::Union(t) => t.iter().for_each(|x| add_term(x, db, v, scope.clone())),
            // There shouldn't be any scopes needing lowering in function arguments
            Term::Fun(_, _, t) => add_term(t, db, v, scope),
            Term::CaseOf(val, cases) => {
                add_term(val, db, v, scope.clone());
                cases
                    .iter()
                    .for_each(|(_, body)| add_term(body, db, v, scope.clone()));
            }
            Term::Unit
            | Term::Var(_)
            | Term::I32(_)
            | Term::Type(_)
            | Term::Builtin(_)
            | Term::Binder(_, None)
            | Term::Cons(_, _) => (),
        }
    }

    fn add_scope(db: &dyn MainGroup, v: &mut Vec<ScopeId>, scope: ScopeId) {
        v.push(scope.clone());
        for Def(_, val) in db.defs(scope.clone()).iter() {
            add_term(val, db, v, scope.clone());
        }
    }

    let mut v = Vec::new();
    add_scope(db, &mut v, ScopeId::File(file));

    Arc::new(
        v.into_iter()
            .skip(1)
            .chain(std::iter::once(ScopeId::File(file)))
            .collect(),
    )
}

fn mangle(db: &dyn MainGroup, scope: ScopeId, s: Sym) -> Option<String> {
    // Return None if it doesn't exist
    let _term = db.term(scope.clone(), s)?;

    // We might mangle types too later

    let b = db.bindings();
    Some(format!("{}${}_{}", b.resolve(s), s.num(), scope.file()))
}

fn low_def(db: &dyn MainGroup, scope: ScopeId, s: Sym) -> Option<LowDef> {
    let elab = db.elab(scope.clone(), s)?;
    let name = db.mangle(scope.clone(), s)?;

    let scoped = (scope, db);

    let mut lctx = LCtx::from(ECtx::new(&scoped));

    let ty = elab.get_type(&scoped).cps_ty(&lctx);
    let cont = lctx.next_val(Ty::Cont);

    let ret = lctx.next_val(ty.clone());
    let body = elab.cps(
        ret,
        &mut lctx,
        crate::backend::low::Low::ContCall(cont, ty, ret),
    );

    if db.options().show_low_ir {
        eprintln!(
            "{}",
            Doc::start("fun")
                .style(Style::Keyword)
                .space()
                .chain(s.pretty(&db))
                .add("(")
                .chain(Ty::Cont.pretty())
                .space()
                .add(cont)
                .add(")")
                .space()
                .add("{")
                .line()
                .chain(body.pretty())
                .indent()
                .line()
                .add("}")
                .ansi_string()
        );
    }

    Some(LowDef { name, cont, body })
}

fn low_mod(db: &dyn MainGroup, file: FileId) -> LowMod {
    for s in db.symbols(ScopeId::File(file)).iter() {
        db.elab(ScopeId::File(file), **s);
    }
    if db.has_errors() {
        return LowMod {
            name: String::from("error"),
            defs: Vec::new(),
            main: None,
        };
    }
    let defs = db
        .child_scopes(file)
        .iter()
        .flat_map(|s| {
            db.symbols(s.clone())
                .iter()
                .map(|n| (s.clone(), **n))
                .collect::<Vec<(ScopeId, Sym)>>()
        })
        .filter_map(|(scope, n)| db.low_def(scope, n))
        .collect();
    let main_raw = db.bindings_mut().raw("main".to_string());
    let main = if let Some(main) = db
        .symbols(ScopeId::File(file))
        .iter()
        .find(|x| x.raw() == main_raw)
    {
        db.mangle(ScopeId::File(file), **main)
    } else {
        None
    };
    LowMod {
        name: String::from("test_mod"),
        defs,
        main,
    }
}

fn symbols(db: &dyn MainGroup, scope: ScopeId) -> Arc<Vec<Spanned<Sym>>> {
    Arc::new(db.defs(scope).iter().map(|Def(x, _)| x.clone()).collect())
}

fn defs(db: &dyn MainGroup, scope: ScopeId) -> Arc<Vec<Def>> {
    let r = match scope {
        ScopeId::File(file) => {
            // We reset the bindings when we get all the definitions so they're more reproducible and thus memoizable
            db.reset();

            let parser = DefsParser::new();
            let s = db.source(file);
            Arc::new(match parser.parse(&s, Lexer::new(&s)) {
                Ok(x) => db
                    .bindings_mut()
                    .resolve_defs(x)
                    .into_iter()
                    .filter_map(|x| match x {
                        Ok(x) => Some(x),
                        Err(e) => {
                            db.error(e.to_error(file));
                            None
                        }
                    })
                    .collect(),
                Err(e) => {
                    db.error(Error::from_lalrpop(e, file));
                    Vec::new()
                }
            })
        }
        ScopeId::Struct(id, _) => db
            .struct_defs(scope.file(), id)
            .unwrap_or_else(|| Arc::new(Vec::new())),
    };

    let mut seen: Vec<Spanned<RawSym>> = Vec::new();
    for Def(sym, _) in r.iter() {
        if let Some(s) = seen.iter().find(|x| ***x == sym.raw()) {
            db.error(
                TypeError::DuplicateField(s.clone(), sym.copy_span(sym.raw()))
                    .to_error(scope.file(), &db),
            );
        } else {
            seen.push(sym.copy_span(sym.raw()));
        }
    }

    r
}

fn term(db: &dyn MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<STerm>> {
    let r = db
        .defs(scope.clone())
        .iter()
        .find(|Def(x, _y)| **x == s)
        .map(|Def(_x, y)| Arc::new(y.clone()));
    if let None = r {
        if let ScopeId::Struct(_, parent) = scope {
            return db.term(*parent, s);
        }
    }
    r
}

fn elab(db: &dyn MainGroup, scope: ScopeId, s: Sym) -> Option<Arc<Elab>> {
    let term = db.term(scope.clone(), s)?;

    let scoped = (scope.clone(), db);
    let mut tctx = TCtx::new(&scoped);

    // If it calls itself recursively, assume it could be anything. We'll use a metavariable for that.
    let name = format!("<type of {}>", s.pretty(&tctx).raw_string());
    let meta = tctx.bindings_mut().create(name);
    tctx.metas.insert(meta, term.span());
    tctx.set_ty(s, Elab::Var(term.span(), meta, Box::new(Elab::Top)));

    let e = check(
        &term,
        &Elab::Var(term.span(), meta, Box::new(Elab::Top)),
        &mut tctx,
    );
    match e {
        Ok(e) => {
            for err in tctx.solve_metas() {
                db.error(err.to_error(scope.file(), &db));
            }

            if let Err(e) = e.check_affine(&mut crate::affine::ACtx::new(&scoped)) {
                db.error(e);
            }
            // We let it go anyway so we don't get "type not found" errors when borrow checking fails
            // We'll check if db.has_errors() before going too far

            // We have to make sure any meta solutions are applied to the term
            let e = e.save_ctx(&mut tctx);
            Some(Arc::new(e))
        }
        Err(e) => {
            db.error(e.to_error(scope.file(), &db));
            None
        }
    }
}

#[salsa::database(MainStorage)]
#[derive(Default)]
pub struct MainDatabase {
    storage: salsa::Storage<Self>,
    bindings: Arc<RwLock<Bindings>>,
    errors: RwLock<Vec<Error>>,
    scopes: RwLock<HashMap<(FileId, StructId), Arc<Vec<Def>>>>,
    builtins: Cell<Option<Builtins>>,
}

impl MainDatabase {
    pub fn emit_errors(&self) {
        self.errors
            .write()
            .unwrap()
            .drain(..)
            .for_each(|e| e.write().unwrap());
    }
}

impl salsa::Database for MainDatabase {}

impl HasBindings for MainDatabase {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        &self.bindings
    }
}

impl MainExt for MainDatabase {
    fn builtins(&self) -> Builtins {
        if let Some(b) = self.builtins.get() {
            b
        } else {
            let b = Builtins::create(self, 0);
            self.builtins.set(Some(b));
            b
        }
    }

    fn reset(&self) {
        self.bindings_mut().reset();
        self.builtins.set(None);
    }

    fn has_errors(&self) -> bool {
        !self.errors.read().unwrap().is_empty()
    }

    fn error(&self, error: Error) {
        self.errors.write().unwrap().push(error);
    }

    fn add_mod(&self, id: StructId, file: FileId, defs: &[(Spanned<Sym>, STerm)]) {
        let defs = defs
            .iter()
            .map(|(name, val)| Def(name.clone(), val.clone()))
            .collect();
        self.scopes
            .write()
            .unwrap()
            .insert((file, id), Arc::new(defs));
    }

    fn struct_defs(&self, file: FileId, id: StructId) -> Option<Arc<Vec<Def>>> {
        self.scopes.read().unwrap().get(&(file, id)).cloned()
    }
}
