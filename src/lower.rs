//! This module deals with translation to Durin.

use std::collections::HashMap;
use smallvec::smallvec;
use durin::ir;
use crate::term::*;
use crate::query::*;

pub struct LCxt<'db> {
    db: &'db dyn Compiler,
    cxt: Cxt,
    locals: IVec<ir::Val>,
    defs: HashMap<PreDefId, ir::Val>,
    builder: Builder<'db>,
}
impl<'db> LCxt<'db> {
    pub fn new(db: &'db dyn Compiler, cxt: Cxt, m: &'db mut ir::Module) -> Self {
        let builder = Builder::new(m);
        LCxt {
            db,
            cxt,
            locals: IVec::new(),
            defs: HashMap::new(),
            builder,
        }
    }
}

/// Takes care of the transformation from direct style to CPS.
struct Builder<'m> {
    module: &'m mut ir::Module,
    block: ir::Val,
    params: Vec<ir::Val>,
    /// (block, params, cont)
    funs: Vec<(ir::Val, Vec<ir::Val>, ir::Val)>,
}
impl<'m> Builder<'m> {
    fn new(m: &'m mut ir::Module) -> Self {
        let block = m.reserve(None);
        Builder {
            module: m,
            block,
            params: Vec::new(),
            funs: Vec::new(),
        }
    }

    fn call(&mut self, f: ir::Val, x: ir::Val) -> ir::Val {
        let cont = self.module.reserve(None);
        self.module.replace(self.block, ir::Node::Fun(ir::Function {
            params: self.params.drain(0..).collect(),
            callee: f,
            call_args: smallvec![x, cont],
        }));
        self.block = cont;
        self.params.push(todo!("type"));
        self.module.add(ir::Node::Param(cont, 0), None)
    }

    fn cons(&mut self, c: ir::Constant) -> ir::Val {
        self.module.add(ir::Node::Const(c), None)
    }

    fn fun_type(&mut self, from: ir::Val, to: ir::Val) -> ir::Val {
        let cont_ty = self.module.add(ir::Node::FunType(smallvec![to]), None);
        self.module.add(ir::Node::FunType(smallvec![from, cont_ty]), None)
    }

    fn reserve(&mut self, name: Option<String>) -> ir::Val {
        self.module.reserve(name)
    }

    /// Returns the parameter value
    fn push_fun(&mut self, param: Option<String>, param_ty: ir::Val, ret_ty: ir::Val) -> ir::Val {
        let fun = self.module.reserve(None);
        let cont = self.module.add(ir::Node::Param(fun, 1), None);
        self.funs.push((self.block, self.params.clone(), cont));
        self.block = fun;
        let cont_ty = self.module.add(ir::Node::FunType(smallvec![ret_ty]), None);
        self.params = vec![param_ty, cont_ty];
        self.module.add(ir::Node::Param(fun, 0), None)
    }

    fn pop_fun(&mut self, ret: ir::Val) -> ir::Val {
        let (block, params, cont) = self.funs.pop().unwrap();
        let fun = self.block;
        // We don't use self.call since we don't add the cont parameter here
        self.module.replace(fun, ir::Node::Fun(ir::Function {
            params: self.params.drain(0..).collect(),
            callee: cont,
            call_args: smallvec![cont],
        }));
        self.block = block;
        self.params = params;
        fun
    }
}

impl Term {
    pub fn lower(&self, cxt: &mut LCxt, ty: &Ty) -> ir::Val {
        match self {
            Term::Type => cxt.builder.cons(ir::Constant::TypeType),
            Term::Var(v) => match v {
                Var::Local(i) => *cxt.locals.get(*i),
                Var::Top(i) => {
                    let (i, _) = cxt.db.lookup_intern_def(*i);
                    *cxt.defs.get(&i).unwrap()
                }
                Var::Rec(i) => *cxt.defs.get(i).unwrap(),
                Var::Meta(m) => todo!("how are global meta solutions handled?"),
            }
            // \x.f x
            // -->
            // fun a (x, r) = f x k
            // fun k y = r y
            Term::Lam(name, _icit, body) => {
                let (param_ty, ret_ty) = match ty {
                    Term::Fun(from, to) => (from, to),
                    Term::Pi(_, _, from, to) => (from, to),
                    _ => unreachable!(),
                };
                let param_ty = param_ty.lower(cxt, &Term::Type);
                let ret_ty_ = ret_ty.lower(cxt, &Term::Type);
                let arg = cxt.builder.push_fun(Some(cxt.db.lookup_intern_name(*name)), param_ty, ret_ty_);
                cxt.locals.add(arg);
                let ret = body.lower(cxt, ret_ty);
                cxt.locals.remove();
                cxt.builder.pop_fun(ret)
            }
            Term::App(_icit, f, x) => {
                let f = f.lower(cxt, &Term::Fun(todo!("x type"), Box::new(ty.clone())));
                let x = x.lower(cxt, todo!("x type"));
                cxt.builder.call(f, x)
            }
            Term::Fun(from, to) => {
                let from = from.lower(cxt, &Term::Type);
                let to = to.lower(cxt, &Term::Type);
                cxt.builder.fun_type(from, to)
            }
            Term::Pi(_n, _i, from, to) => {
                todo!("pi types in Durin")
            }
            Term::Error => panic!("type errors should have been caught by now!"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let buf = String::from(r#"
            fun f (x : Type) = x
            fun g (y : Type) = f y
        "#);
        let mut db = Database::default();
        let id = crate::error::FILES.write().unwrap().add("file_name".into(), buf.clone());
        db.set_file_source(id, buf);
        let mut m = ir::Module::default();
        let cxt = db.cxt_entry(MaybeEntry::No(id));
        let mut lcxt = LCxt::new(&db, cxt, &mut m);
        for &def in &*db.top_level(id) {
            let mcxt = crate::elaborate::MCxt::new(cxt, def, &db);
            if let Ok(def) = db.elaborate_def(def) {
                def.term.lower(&mut lcxt, &crate::evaluate::quote((*def.typ).clone(), Lvl::zero(), &mcxt));
            }
        }
        println!("module: {}", lcxt.builder.module.emit());
        panic!("done")
    }
}
