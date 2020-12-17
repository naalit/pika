//! This module deals with translation to Durin.

use crate::common::*;
use crate::elaborate::MCxt;
use crate::error::FileId;
use crate::term::*;
use durin::builder::*;
use durin::ir;

use smallvec::SmallVec;
use std::collections::HashMap;

pub struct ModCxt<'m> {
    db: &'m dyn Compiler,
    defs: HashMap<PreDefId, (IVec<ir::Val>, ir::Val)>,
    scope_ids: HashMap<PreDefId, ScopeId>,
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
            scope_ids: HashMap::new(),
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
            &mut self.scope_ids,
            locals,
        );
        let val = f(&mut lcxt);
        lcxt.builder.finish();

        let val2 = lcxt.get_or_reserve(pre);
        self.module.redirect(val2, val);
    }
}

pub struct LCxt<'db> {
    db: &'db dyn Compiler,
    locals: IVec<ir::Val>,
    defs: &'db mut HashMap<PreDefId, (IVec<ir::Val>, ir::Val)>,
    scope_ids: &'db mut HashMap<PreDefId, ScopeId>,
    builder: Builder<'db>,
    mcxt: MCxt,
}
impl<'db> LCxt<'db> {
    fn new(
        db: &'db dyn Compiler,
        mcxt: MCxt,
        m: &'db mut ir::Module,
        defs: &'db mut HashMap<PreDefId, (IVec<ir::Val>, ir::Val)>,
        scope_ids: &'db mut HashMap<PreDefId, ScopeId>,
        locals: IVec<ir::Val>,
    ) -> Self {
        let builder = Builder::new(m);
        LCxt {
            db,
            locals,
            defs,
            scope_ids,
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
    pub fn lower(self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
        self.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db).lower(ty, cxt)
    }
}

pub fn durin(db: &dyn Compiler, file: FileId) -> ir::Module {
    let mut mcxt = ModCxt::new(db);
    let mut stack: Vec<_> = db.top_level(file).iter().copied().rev().collect();
    while let Some(def) = stack.pop() {
        if let Ok(info) = db.elaborate_def(def) {
            mcxt.local(def, |lcxt| info.term.lower((*info.typ).clone(), lcxt));
            stack.extend(info.children.iter().copied());
        }
    }
    mcxt.finish()
}

fn lower_datatype(sid: ScopeId, cxt: &mut LCxt) -> Vec<ir::Val> {
    cxt.db
        .lookup_intern_scope(sid)
        .iter()
        .filter_map(|&(_name, id)| {
            let info = cxt.db.elaborate_def(id).ok()?;
            match &*info.term {
                Term::Var(Var::Cons(cid), _) if id == *cid => {
                    let mut cty: Val = info.typ.into_owned();
                    let mut i = 0;
                    let mut args = Vec::new();
                    loop {
                        match cty {
                            Val::Pi(_, cl) => {
                                let from = cl.ty.clone();
                                // TODO dependent product types and cxt.local()
                                cxt.mcxt
                                    .define(cl.name, NameInfo::Local(from.clone()), cxt.db);
                                args.push(from.lower(Val::Type, cxt));
                                cty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                                i += 1;
                            }
                            Val::Fun(from, to) => {
                                args.push(from.lower(Val::Type, cxt));
                                cty = *to;
                            }
                            _ => break,
                        }
                    }
                    for _ in 0..i {
                        cxt.mcxt.undef(cxt.db);
                    }
                    // if args.len() == 1 {
                    //     Some(args.pop().unwrap())
                    // } else {
                    Some(cxt.builder.prod_type(args))
                    // }
                }
                _ => None,
            }
        })
        .collect()
}

impl Term {
    pub fn lower(&self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
        match self {
            Term::Type => cxt.builder.cons(ir::Constant::TypeType),
            Term::Var(v, _) => match v {
                Var::Local(i) => *cxt.locals.get(*i),
                Var::Top(i) => {
                    let (i, _) = cxt.db.lookup_intern_def(*i);
                    cxt.get_or_reserve(i)
                }
                Var::Rec(i) => cxt.get_or_reserve(*i),
                Var::Meta(_) => panic!("unsolved meta passed to lower()"),
                Var::Type(tid, sid) => {
                    let (pre, _) = cxt.db.lookup_intern_def(*tid);
                    cxt.scope_ids.insert(pre, *sid);

                    let conses = lower_datatype(*sid, cxt);
                    let mut ty = ty;
                    let mut funs = Vec::new();
                    loop {
                        match ty {
                            Val::Pi(_, cl) => {
                                let from = cl.ty.clone();
                                let lty = from.clone().lower(Val::Type, cxt);
                                let p = cxt.builder.push_fun(None, lty.clone());
                                cxt.local(cl.name, p, from);
                                funs.push((lty, true));
                                ty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                            }
                            Val::Fun(from, to) => {
                                let from = from.lower(Val::Type, cxt);
                                cxt.builder.push_fun(None, from);
                                funs.push((from, false));
                                ty = *to;
                            }
                            _ => break,
                        }
                    }
                    let mut val = cxt.builder.sum_type(conses);
                    for (ty, is_pi) in funs.into_iter().rev() {
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun(val, ty);
                    }
                    val
                }
                Var::Cons(id) => {
                    let &sid = match ty
                        .clone()
                        .ret_type(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                        .unarc()
                    {
                        Val::App(Var::Type(_id, sid), _, _, _) => sid,
                        Val::App(Var::Rec(id), _, _, _) => cxt
                            .scope_ids
                            .get(id)
                            .expect("Datatypes should be lowered before their constructors!"),
                        x => unreachable!("{:?}", x),
                    };

                    let idx = cxt
                        .db
                        .lookup_intern_scope(sid)
                        .iter()
                        .filter_map(|&(_name, id)| {
                            let info = cxt.db.elaborate_def(id).ok()?;
                            match &*info.term {
                                Term::Var(Var::Cons(cid), _) if id == *cid => Some(id),
                                _ => None,
                            }
                        })
                        .enumerate()
                        .find(|(_, x)| x == id)
                        .unwrap()
                        .0;
                    let conses = lower_datatype(sid, cxt);

                    let prod_ty = conses[idx];
                    let sum_ty = cxt.builder.sum_type(conses);

                    // TODO should this Durin-function-from-Pika-type be its own function?
                    let mut ty = ty;
                    let mut funs = Vec::new();
                    loop {
                        match ty {
                            Val::Pi(_, cl) => {
                                let from = cl.ty.clone();
                                let lty = from.clone().lower(Val::Type, cxt);
                                let p = cxt.builder.push_fun(None, lty.clone());
                                cxt.local(cl.name, p, from);
                                funs.push((p, lty, true));
                                ty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                            }
                            Val::Fun(from, to) => {
                                let from = from.lower(Val::Type, cxt);
                                let p = cxt.builder.push_fun(None, from);
                                funs.push((p, from, false));
                                ty = *to;
                            }
                            _ => break,
                        }
                    }
                    let val = cxt.builder.product(
                        prod_ty,
                        funs.iter()
                            .map(|&(x, _, _)| x)
                            .collect::<SmallVec<[ir::Val; 3]>>(),
                    );
                    let mut val = cxt.builder.inject_sum(sum_ty, idx, val);
                    for (_p, ty, is_pi) in funs.into_iter().rev() {
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun(val, ty);
                    }

                    val
                }
            },
            // \x.f x
            // -->
            // fun a (x, r) = f x k
            // fun k y = r y
            Term::Lam(name, _icit, _arg_ty, body) => {
                let (param_ty, ret_ty) = match ty.inline(cxt.mcxt.size, cxt.db, &cxt.mcxt) {
                    Val::Fun(from, to) => (*from, to.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)),
                    Val::Pi(_, cl) => (cl.ty.clone(), cl.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)),
                    _ => unreachable!(),
                };
                assert_eq!(cxt.mcxt.size, cxt.locals.size());
                let param_ty_ = param_ty.clone().lower(Val::Type, cxt);
                let arg = cxt
                    .builder
                    .push_fun(Some(cxt.db.lookup_intern_name(*name)), param_ty_);
                cxt.local(*name, arg, param_ty);
                let ret = body.lower(
                    ret_ty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db),
                    cxt,
                );
                let ret_ty = ret_ty.lower(Val::Type, cxt);
                cxt.pop_local();
                cxt.builder.pop_fun(ret, ret_ty)
            }
            Term::App(_icit, f, fty, x) => {
                let ret_ty = ty;
                let ret_ty = ret_ty.lower(Val::Type, cxt);
                let fty = fty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db);
                let xty = match fty.unarc() {
                    Val::Pi(_, cl) => cl.ty.clone(),
                    Val::Fun(x, _) => (**x).clone(),
                    _ => unreachable!(),
                };
                let f = f.lower(fty, cxt);
                let x = x.lower(xty, cxt);
                cxt.builder.call(f, x, ret_ty)
            }
            Term::Fun(from, to) => {
                let from = from.lower(Val::Type, cxt);
                let to = to.lower(Val::Type, cxt);
                cxt.builder.fun_type(from, to)
            }
            Term::Pi(name, _icit, from, to) => {
                let from_ = from.lower(Val::Type, cxt);
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
                let to = to.lower(Val::Type, cxt);
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
                mcxt.local(def, |lcxt| info.term.lower((*info.typ).clone(), lcxt));
            }
        }
        println!("module: {}", mcxt.module.emit());
    }
}
