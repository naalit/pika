//! This module deals with translation to Durin.

use crate::elaborate::MCxt;
use crate::query::*;
use crate::term::*;
use durin::ir;
use smallvec::smallvec;
use std::collections::HashMap;

pub struct ModCxt<'m> {
    db: &'m dyn Compiler,
    defs: HashMap<PreDefId, ir::Val>,
    module: ir::Module,
}
impl<'m> ModCxt<'m> {
    pub fn new(db: &'m dyn Compiler) -> Self {
        ModCxt {
            db,
            defs: HashMap::new(),
            module: ir::Module::default(),
        }
    }

    pub fn local(&mut self, def: DefId, f: impl FnOnce(&mut LCxt) -> ir::Val) {
        let (pre, cxt) = self.db.lookup_intern_def(def);
        let mut lcxt = LCxt::new(
            self.db,
            MCxt::new(cxt, def, self.db),
            &mut self.module,
            &self.defs,
        );
        let val = f(&mut lcxt);
        let name = self.db.lookup_intern_predef(pre).name();
        self.module
            .set_name(val, name.map(|x| self.db.lookup_intern_name(x)));
        self.defs.insert(pre, val);
    }
}

pub struct LCxt<'db> {
    db: &'db dyn Compiler,
    locals: IVec<ir::Val>,
    defs: &'db HashMap<PreDefId, ir::Val>,
    builder: Builder<'db>,
    mcxt: MCxt,
}
impl<'db> LCxt<'db> {
    fn new(
        db: &'db dyn Compiler,
        mcxt: MCxt,
        m: &'db mut ir::Module,
        defs: &'db HashMap<PreDefId, ir::Val>,
    ) -> Self {
        let builder = Builder::new(m);
        LCxt {
            db,
            locals: IVec::new(),
            defs,
            builder,
            mcxt,
        }
    }
}

struct Pi {
    pub arg: ir::Val,
    from: ir::Val,
}

/// Takes care of the transformation from direct style to CPS.
struct Builder<'m> {
    module: &'m mut ir::Module,
    block: ir::Val,
    params: Vec<ir::Val>,
    /// (fun, block, params, cont)
    funs: Vec<(ir::Val, ir::Val, Vec<ir::Val>, ir::Val)>,
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

    fn call(&mut self, f: ir::Val, x: ir::Val, ret_ty: ir::Val) -> ir::Val {
        let cont = self.module.reserve(None);
        self.module.replace(
            self.block,
            ir::Node::Fun(ir::Function {
                params: self.params.drain(0..).collect(),
                callee: f,
                call_args: smallvec![x, cont],
            }),
        );
        self.block = cont;
        self.params.push(ret_ty);
        self.module.add(ir::Node::Param(cont, 0), None)
    }

    fn cons(&mut self, c: ir::Constant) -> ir::Val {
        self.module.add(ir::Node::Const(c), None)
    }

    fn fun_type(&mut self, from: ir::Val, to: ir::Val) -> ir::Val {
        let cont_ty = self.module.add(ir::Node::FunType(smallvec![to]), None);
        self.module
            .add(ir::Node::FunType(smallvec![from, cont_ty]), None)
    }

    fn start_pi(&mut self, param: Option<String>, from: ir::Val) -> Pi {
        Pi {
            arg: self.module.reserve(param),
            from,
        }
    }

    fn end_pi(&mut self, pi: Pi, to: ir::Val) -> ir::Val {
        let Pi { arg, from } = pi;
        let cont_ty = self.module.add(ir::Node::FunType(smallvec![to]), None);
        let fun = self
            .module
            .add(ir::Node::FunType(smallvec![from, cont_ty]), None);
        self.module.replace(arg, ir::Node::Param(fun, 0));
        fun
    }

    fn reserve(&mut self, name: Option<String>) -> ir::Val {
        self.module.reserve(name)
    }

    /// Returns the parameter value
    fn push_fun(&mut self, param: Option<String>, param_ty: ir::Val, ret_ty: ir::Val) -> ir::Val {
        let fun = self.module.reserve(None);
        let cont = self.module.add(ir::Node::Param(fun, 1), None);
        self.funs.push((fun, self.block, self.params.clone(), cont));
        self.block = fun;
        let cont_ty = self.module.add(ir::Node::FunType(smallvec![ret_ty]), None);
        self.params = vec![param_ty, cont_ty];
        self.module.add(ir::Node::Param(fun, 0), param)
    }

    fn pop_fun(&mut self, ret: ir::Val) -> ir::Val {
        let (fun, block, params, cont) = self.funs.pop().unwrap();
        // We don't use self.call since we don't add the cont parameter here
        self.module.replace(
            self.block,
            ir::Node::Fun(ir::Function {
                params: self.params.drain(0..).collect(),
                callee: cont,
                call_args: smallvec![ret],
            }),
        );
        self.block = block;
        self.params = params;
        fun
    }
}

impl Val {
    pub fn lower(self, cxt: &mut LCxt) -> ir::Val {
        crate::evaluate::quote(self, cxt.mcxt.size, &cxt.mcxt).lower(cxt)
    }
}

impl Term {
    pub fn lower(&self, cxt: &mut LCxt) -> ir::Val {
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
            },
            // \x.f x
            // -->
            // fun a (x, r) = f x k
            // fun k y = r y
            Term::Lam(name, _icit, _arg_ty, body) => {
                let (param_ty, ret_ty) = match self.ty(&cxt.mcxt, cxt.db) {
                    Val::Fun(from, to) => (*from, *to),
                    Val::Pi(_, from, to) => (*from, to.vquote(cxt.mcxt.size, &cxt.mcxt)),
                    _ => unreachable!(),
                };
                let param_ty = param_ty.lower(cxt);
                let ret_ty_ = ret_ty.lower(cxt);
                let arg =
                    cxt.builder
                        .push_fun(Some(cxt.db.lookup_intern_name(*name)), param_ty, ret_ty_);
                cxt.locals.add(arg);
                let ret = body.lower(cxt);
                cxt.locals.remove();
                cxt.builder.pop_fun(ret)
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
                let from = from.lower(cxt);
                let pi = cxt
                    .builder
                    .start_pi(Some(cxt.db.lookup_intern_name(*name)), from);
                cxt.locals.add(pi.arg);
                let to = to.lower(cxt);
                cxt.locals.remove();
                cxt.builder.end_pi(pi, to)
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
