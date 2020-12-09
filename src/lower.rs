//! This module deals with translation to Durin.

use crate::elaborate::MCxt;
use crate::error::FileId;
use crate::query::*;
use crate::term::*;
use durin::builder::*;
use durin::ir;
use std::collections::HashMap;

pub struct ModCxt<'m> {
    db: &'m dyn Compiler,
    defs: HashMap<PreDefId, (IVec<ir::Val>, ir::Val)>,
    module: ir::Module,
}
impl<'m> ModCxt<'m> {
    pub fn finish(self) -> ir::Module {
        self.module
    }

    pub fn new(db: &'m dyn Compiler) -> Self {
        ModCxt {
            db,
            defs: HashMap::new(),
            module: ir::Module::default(),
        }
    }

    pub fn local(&mut self, def: DefId, f: impl FnOnce(&mut LCxt) -> ir::Val) {
        let (pre, cxt) = self.db.lookup_intern_def(def);
        let locals = match self.defs.get(&pre) {
            Some((l, _)) => l.clone(),
            None => IVec::new(),
        };
        let mut lcxt = LCxt::new(
            self.db,
            MCxt::new(cxt, def, self.db),
            &mut self.module,
            &mut self.defs,
            locals,
        );
        let val = f(&mut lcxt);
        lcxt.builder.finish();

        let val2 = lcxt.get_or_reserve(pre);
        let node = self.module.get(val).unwrap().clone();
        self.module.replace(val2, node);
    }
}

pub struct LCxt<'db> {
    db: &'db dyn Compiler,
    locals: IVec<ir::Val>,
    defs: &'db mut HashMap<PreDefId, (IVec<ir::Val>, ir::Val)>,
    builder: Builder<'db>,
    mcxt: MCxt,
}
impl<'db> LCxt<'db> {
    fn new(
        db: &'db dyn Compiler,
        mcxt: MCxt,
        m: &'db mut ir::Module,
        defs: &'db mut HashMap<PreDefId, (IVec<ir::Val>, ir::Val)>,
        locals: IVec<ir::Val>,
    ) -> Self {
        let builder = Builder::new(m);
        LCxt {
            db,
            locals,
            defs,
            builder,
            mcxt,
        }
    }

    pub fn local(&mut self, name: Name, val: ir::Val, ty: VTy) {
        self.locals.add(val);
        self.mcxt.define(name, NameInfo::Local(ty), self.db);
    }

    pub fn pop_local(&mut self) {
        self.locals.remove();
        self.mcxt.undef(self.db);
    }

    pub fn get_or_reserve(&mut self, def: PreDefId) -> ir::Val {
        if let Some((_, x)) = self.defs.get(&def) {
            *x
        } else {
            let pre = self.db.lookup_intern_predef(def);
            let name = pre.name().map(|x| x.get(self.db));
            let x = self.builder.reserve(name);
            self.defs.insert(def, (self.locals.clone(), x));
            x
        }
    }
}

impl Val {
    pub fn lower(self, cxt: &mut LCxt) -> ir::Val {
        self.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db).lower(cxt)
    }
}

pub fn durin(db: &dyn Compiler, file: FileId) -> ir::Module {
    let mut mcxt = ModCxt::new(db);
    let mut stack: Vec<_> = db.top_level(file).iter().copied().rev().collect();
    while let Some(def) = stack.pop() {
        if let Ok(info) = db.elaborate_def(def) {
            mcxt.local(def, |lcxt| info.term.lower(lcxt));
            stack.extend(info.children.iter().copied());
        }
    }
    mcxt.finish()
}

impl Term {
    pub fn lower(&self, cxt: &mut LCxt) -> ir::Val {
        match self {
            Term::Type => cxt.builder.cons(ir::Constant::TypeType),
            Term::Var(v) => match v {
                Var::Local(i) => *cxt.locals.get(*i),
                Var::Top(i) => {
                    let (i, _) = cxt.db.lookup_intern_def(*i);
                    cxt.get_or_reserve(i)
                }
                Var::Rec(i) => cxt.get_or_reserve(*i),
                Var::Meta(_) => panic!("unsolved meta passed to lower()"),
                Var::Type(_, _) | Var::Cons(_) => todo!("lowering datatypes"),
            },
            // \x.f x
            // -->
            // fun a (x, r) = f x k
            // fun k y = r y
            Term::Lam(name, _icit, _arg_ty, body) => {
                let (param_ty, ret_ty) = match self.ty(&cxt.mcxt, cxt.db) {
                    Val::Fun(from, to) => (*from, to.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)),
                    Val::Pi(_, from, to) => (*from, to.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)),
                    _ => unreachable!(),
                };
                assert_eq!(cxt.mcxt.size, cxt.locals.size());
                let param_ty_ = param_ty.clone().lower(cxt);
                let arg = cxt
                    .builder
                    .push_fun(Some(cxt.db.lookup_intern_name(*name)), param_ty_);
                cxt.local(*name, arg, param_ty);
                let ret_ty = ret_ty.lower(cxt);
                let ret = body.lower(cxt);
                cxt.pop_local();
                cxt.builder.pop_fun(ret, ret_ty)
            }
            Term::App(_icit, f, x) => {
                let ret_ty = self.ty(&cxt.mcxt, cxt.db);
                let ret_ty = ret_ty.lower(cxt);
                let f = f.lower(cxt);
                let x = x.lower(cxt);
                cxt.builder.call(f, x, ret_ty)
            }
            Term::Fun(from, to) => {
                let from = from.lower(cxt);
                let to = to.lower(cxt);
                cxt.builder.fun_type(from, to)
            }
            Term::Pi(name, _icit, from, to) => {
                let from_ = from.lower(cxt);
                let pi = cxt
                    .builder
                    .start_pi(Some(cxt.db.lookup_intern_name(*name)), from_);
                cxt.local(
                    *name,
                    pi.arg,
                    (**from)
                        .clone()
                        .evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db),
                );
                let to = to.lower(cxt);
                cxt.pop_local();
                cxt.builder.end_pi(pi, to)
            }
            Term::Error => panic!("type errors should have been caught by now!"),
            Term::Case(_, _) => todo!("lowering case"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let buf = String::from(
            r#"
            fun f (x : Type) = x
            fun g (y : Type) = f y
        "#,
        );
        let mut db = Database::default();
        let id = crate::error::FILES
            .write()
            .unwrap()
            .add("file_name".into(), buf.clone());
        db.set_file_source(id, buf);
        let mut mcxt = ModCxt::new(&db);
        for &def in &*db.top_level(id) {
            if let Ok(info) = db.elaborate_def(def) {
                mcxt.local(def, |lcxt| info.term.lower(lcxt));
            }
        }
        println!("module: {}", mcxt.module.emit());
    }
}
