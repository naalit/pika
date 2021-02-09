//! This module deals with translation to Durin.

use crate::elaborate::{MCxt, MCxtType};
use crate::error::FileId;
use crate::term::*;
use crate::{common::*, pattern::Pat};
use durin::builder::*;
use durin::ir;

use smallvec::SmallVec;
use std::collections::HashMap;

pub struct ModCxt<'m> {
    db: &'m dyn Compiler,
    defs: HashMap<PreDefId, ir::Val>,
    scope_ids: HashMap<PreDefId, (DefId, ScopeId)>,
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
        let (pre, cxt, _) = self.db.lookup_intern_def(def);
        let locals = IVec::new();
        let mut lcxt = LCxt::new(
            self.db,
            MCxt::new(cxt, MCxtType::Local(def), self.db),
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
    defs: &'db mut HashMap<PreDefId, ir::Val>,
    scope_ids: &'db mut HashMap<PreDefId, (DefId, ScopeId)>,
    if_state: Vec<ir::Val>,
    rcont: Option<ir::Val>,
    builder: Builder<'db>,
    mcxt: MCxt,
    eff_conts: Vec<ir::Val>,
}
impl<'db> LCxt<'db> {
    fn new(
        db: &'db dyn Compiler,
        mcxt: MCxt,
        m: &'db mut ir::Module,
        defs: &'db mut HashMap<PreDefId, ir::Val>,
        scope_ids: &'db mut HashMap<PreDefId, (DefId, ScopeId)>,
        locals: IVec<ir::Val>,
    ) -> Self {
        let builder = Builder::new(m);
        LCxt {
            db,
            locals,
            defs,
            scope_ids,
            if_state: Vec::new(),
            rcont: None,
            builder,
            mcxt,
            eff_conts: Vec::new(),
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

    pub fn eff(&mut self, ty: Val, cont: ir::Val) {
        // Make sure they're in sync, so you can just use pop_eff() and pop_scope() normally
        self.eff_conts.truncate(self.mcxt.eff_stack.len());
        self.mcxt.eff_stack.push_eff(ty);
        self.eff_conts.push(cont);
    }

    pub fn get_or_reserve(&mut self, def: PreDefId) -> ir::Val {
        if let Some(x) = self.defs.get(&def) {
            *x
        } else {
            let pre = self.db.lookup_intern_predef(def);
            let name = pre.name().map(|x| x.get(self.db));
            let x = self.builder.reserve(name);
            self.defs.insert(def, x);
            x
        }
    }

    pub fn ifcase(&mut self, case: usize, scrutinee: ir::Val, case_ty: ir::Val) -> ir::Val {
        // Stored in opposite order to the arguments to the if cont
        if let Some(k) = self.rcont {
            self.if_state.push(k);
        }
        for &k in self.eff_conts
            [self.mcxt.eff_stack.scope_start().unwrap_or(0)..self.mcxt.eff_stack.len()]
            .iter()
            .rev()
        {
            self.if_state.push(k);
        }
        self.builder.ifcase(case, scrutinee, case_ty)
    }

    pub fn if_expr(&mut self, cond: ir::Val) {
        self.builder.if_expr(cond);
        // Stored in opposite order to the arguments to the if cont
        if let Some(k) = self.rcont {
            self.if_state.push(k);
        }
        for &k in self.eff_conts
            [self.mcxt.eff_stack.scope_start().unwrap_or(0)..self.mcxt.eff_stack.len()]
            .iter()
            .rev()
        {
            self.if_state.push(k);
        }
    }

    /// Switches from the `then` block, which returns the given expression, to the `else` block.
    pub fn otherwise(&mut self, ret: ir::Val) {
        let mut rets = vec![ret];
        for k in &mut self.eff_conts
            [self.mcxt.eff_stack.scope_start().unwrap_or(0)..self.mcxt.eff_stack.len()]
        {
            rets.push(*k);
            *k = self.if_state.pop().unwrap();
        }
        if let Some(k) = &mut self.rcont {
            rets.push(*k);
            *k = self.if_state.pop().unwrap();
        }
        self.builder.otherwise(rets);
    }

    /// Ends an `else` block, returning the expression.
    pub fn endif(&mut self, ret: ir::Val, ret_ty: ir::Val) -> ir::Val {
        let mut rets = vec![(ret, ret_ty)];
        for &k in &self.eff_conts
            [self.mcxt.eff_stack.scope_start().unwrap_or(0)..self.mcxt.eff_stack.len()]
        {
            rets.push((k, self.builder.type_of(k)));
        }
        if let Some(k) = self.rcont {
            let any_ty = self.builder.cons(ir::Constant::TypeType);
            rets.push((k, self.builder.fun_type_raw(&[any_ty] as &_)));
        }
        let vals = self.builder.endif(&rets);

        let mut vals = vals.into_iter();
        let ret = vals.next().unwrap();
        for k in &mut self.eff_conts
            [self.mcxt.eff_stack.scope_start().unwrap_or(0)..self.mcxt.eff_stack.len()]
        {
            *k = vals.next().unwrap();
        }
        if let Some(k) = &mut self.rcont {
            *k = vals.next().unwrap();
        }

        ret
    }
}

impl Val {
    pub fn lower(self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
        // If this is a datatype applied to all its arguments, inline the sum type
        // That way Durin knows the type when calling ifcase
        let (tid, sid, targs) = match self {
            Val::App(Var::Type(tid, sid), _, sp, _) => {
                (tid, sid, sp.into_iter().map(|(_, v)| v).collect())
            }
            Val::App(Var::Top(tid), hty, sp, g) => {
                if let Some(&(x, y)) = cxt.scope_ids.get(&cxt.db.lookup_intern_def(tid).0) {
                    (x, y, sp.into_iter().map(|(_, v)| v).collect())
                } else {
                    return Val::App(Var::Top(tid), hty, sp, g)
                        .quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                        .lower(ty, cxt);
                }
            }
            Val::App(Var::Rec(id), hty, sp, g) => {
                if let Some(&(x, y)) = cxt.scope_ids.get(&id) {
                    (x, y, sp.into_iter().map(|(_, v)| v).collect())
                } else {
                    return Val::App(Var::Rec(id), hty, sp, g)
                        .quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                        .lower(ty, cxt);
                }
            }
            Val::Arc(x) => return IntoOwned::<Val>::into_owned(x).lower(ty, cxt),
            x => return x.quote(cxt.mcxt.size, &cxt.mcxt, cxt.db).lower(ty, cxt),
        };
        let (tys, _) = lower_datatype(tid, sid, targs, cxt);
        cxt.builder.sum_type(tys)
    }
}

pub fn durin(db: &dyn Compiler, file: FileId) -> ir::Module {
    let mut mcxt = ModCxt::new(db);
    for &def in &*db.top_level(file) {
        if let Ok(info) = db.elaborate_def(def) {
            mcxt.local(def, |lcxt| {
                let val = info.term.lower((*info.typ).clone(), lcxt);
                lower_children(def, lcxt);
                val
            });
        }
    }
    mcxt.finish()
}

fn lower_children(def: DefId, cxt: &mut LCxt) {
    let mut stack = match cxt.db.elaborate_def(def) {
        Ok(info) => (*info.children).clone(),
        _ => return,
    };
    while let Some(def) = stack.pop() {
        if let Ok(info) = cxt.db.elaborate_def(def) {
            let (pre_id, _cxt, _) = cxt.db.lookup_intern_def(def);
            let val = info.term.lower((*info.typ).clone(), cxt);
            let val2 = cxt.get_or_reserve(pre_id);
            cxt.builder.redirect(val2, val);

            stack.extend(info.children.iter().copied());
        }
    }
}

/// Returns (constructor return types, whether each parameter of the constructor should be kept)
fn lower_datatype(
    tid: DefId,
    sid: ScopeId,
    targs: Vec<Val>,
    cxt: &mut LCxt,
) -> (Vec<ir::Val>, Vec<Vec<bool>>) {
    cxt.db
        .lookup_intern_scope(sid)
        .iter()
        .filter_map(|&(_name, id)| {
            let info = cxt.db.elaborate_def(id).ok()?;
            match &*info.term {
                Term::Var(Var::Cons(cid), _) if id == *cid => {
                    let mut cty: Val = info.typ.into_owned();
                    let solutions = {
                        let start_state = cxt.mcxt.state();

                        // First define the locals from the type
                        let mut tty: Val = cxt.db.elaborate_def(tid).unwrap().typ.into_owned();
                        let mut ty_args = Vec::new();
                        loop {
                            match tty {
                                Val::Pi(i, cl) => {
                                    let from = cl.ty.clone();
                                    cxt.mcxt
                                        .define(cl.name, NameInfo::Local(from.clone()), cxt.db);
                                    ty_args.push((i, Val::local(cxt.mcxt.size, from)));
                                    tty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                                }
                                Val::Fun(_, _) => unreachable!("Datatypes must have pi types"),
                                _ => break,
                            }
                        }
                        let tty = Val::App(
                            Var::Type(tid, sid),
                            Box::new(cxt.db.elaborate_def(tid).unwrap().typ.into_owned()),
                            ty_args,
                            Glued::new(),
                        );

                        // Then define the ones from the constructor type
                        let lbefore = cxt.mcxt.size;
                        // We need to move the constructor type inside of the abstractions from the datatype
                        let mut cty = cty
                            .clone()
                            .quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                            .evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db);
                        loop {
                            match cty {
                                Val::Pi(_, cl) => {
                                    let from = cl.ty.clone();
                                    cxt.mcxt
                                        .define(cl.name, NameInfo::Local(from.clone()), cxt.db);
                                    cty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                                }
                                Val::Fun(_from, to) => {
                                    // This argument can't be used in the type, so we skip it
                                    cty = *to;
                                }
                                Val::With(_, mut v) => {
                                    assert_eq!(v.len(), 1);
                                    cty = v.pop().unwrap();
                                }
                                _ => break,
                            }
                        }

                        // Now unify
                        if !crate::elaborate::local_unify(
                            tty,
                            cty,
                            cxt.mcxt.size,
                            Span::empty(),
                            cxt.db,
                            &mut cxt.mcxt,
                        )
                        .unwrap_or(false)
                        {
                            panic!("Unification of datatype with constructor return type failed!")
                        }

                        // Then add the arguments passed to the type this time
                        let mut env = Env::new(start_state.size);
                        for i in &targs {
                            env.push(Some(i.clone()));
                        }
                        assert_eq!(env.size, lbefore);

                        // And for each constructor pi-parameter, add the constraint to `solutions` if it exists
                        let mut l = lbefore;
                        let mut solutions: Vec<Option<Val>> = Vec::new();
                        while l <= cxt.mcxt.size {
                            l = l.inc();
                            if let Some(v) = cxt.mcxt.local_val(l) {
                                let v = v
                                    .clone()
                                    .quote(env.size, &cxt.mcxt, cxt.db)
                                    .evaluate(&env, &cxt.mcxt, cxt.db);
                                solutions.push(Some(v));
                            } else {
                                solutions.push(None);
                            }
                        }
                        cxt.mcxt.set_state(start_state);
                        solutions
                    };

                    // Now generate the sigma type representing the constructor
                    let mut i = 0;
                    let mut sigma = cxt.builder.sigma();
                    let mut keep = Vec::new();
                    let mut env = Env::new(cxt.mcxt.size);
                    loop {
                        assert_eq!(env.size, cxt.mcxt.size);
                        match cty {
                            Val::Pi(_, cl) => {
                                // Quote-evaluate to apply substitutions from the environment
                                let from = cl
                                    .ty
                                    .clone()
                                    .quote(env.size, &cxt.mcxt, cxt.db)
                                    .evaluate(&env, &cxt.mcxt, cxt.db);

                                let val = if let Some(x) = &solutions[i] {
                                    keep.push(false);
                                    // Add the solution to the environment
                                    env.push(Some(x.clone()));
                                    // If we solved it, skip adding it to the sigma
                                    // This shouldn't be used at all
                                    cxt.builder.cons(ir::Constant::Unreachable)
                                } else {
                                    // It doesn't have a solution, so it remains in the product type
                                    keep.push(true);
                                    env.push(None);
                                    sigma.add(from.clone().lower(Val::Type, cxt), &mut cxt.builder)
                                };

                                // Define the variable and go to the next level
                                cxt.local(cl.name, val, from);
                                cty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                                i += 1;
                            }
                            Val::Fun(from, to) => {
                                // Quote-evaluate to apply substitutions from the environment
                                let from = from
                                    .quote(env.size, &cxt.mcxt, cxt.db)
                                    .evaluate(&env, &cxt.mcxt, cxt.db);

                                // We know we're keeping this one, since we can't solve a non-pi parameter
                                keep.push(true);

                                // Don't add the parameter to the context, since it's not a pi
                                sigma.add(from.clone().lower(Val::Type, cxt), &mut cxt.builder);
                                cty = *to;
                            }
                            _ => break,
                        }
                    }
                    for _ in 0..i {
                        cxt.pop_local();
                    }
                    Some((sigma.finish(&mut cxt.builder), keep))
                }
                _ => None,
            }
        })
        .unzip()
}

impl BinOp {
    fn lower(self) -> ir::BinOp {
        match self {
            BinOp::Add => ir::BinOp::IAdd,
            BinOp::Sub => ir::BinOp::ISub,
            BinOp::Mul => ir::BinOp::IMul,
            BinOp::Div => ir::BinOp::IDiv,
            BinOp::Exp => ir::BinOp::IExp,
            BinOp::BitAnd => ir::BinOp::IAnd,
            BinOp::BitOr => ir::BinOp::IOr,
            BinOp::BitXor => ir::BinOp::IXor,
            BinOp::BitShl => ir::BinOp::IShl,
            BinOp::BitShr => ir::BinOp::IShr,

            BinOp::Eq => ir::BinOp::IEq,
            BinOp::NEq => ir::BinOp::INEq,
            BinOp::Lt => ir::BinOp::ILt,
            BinOp::Gt => ir::BinOp::IGt,
            BinOp::Leq => ir::BinOp::ILeq,
            BinOp::Geq => ir::BinOp::IGeq,

            _ => todo!("lower pipes"),
        }
    }
}

impl Builtin {
    fn lower(self, cxt: &mut LCxt) -> ir::Val {
        match self {
            Builtin::I32 => cxt.builder.cons(ir::Constant::IntType(ir::Width::W32)),
            Builtin::I64 => cxt.builder.cons(ir::Constant::IntType(ir::Width::W64)),
            // Bool translates to i1
            Builtin::Bool => cxt.builder.cons(ir::Constant::IntType(ir::Width::W1)),
            Builtin::BinOp(op) => {
                let i32_ty = cxt.builder.cons(ir::Constant::IntType(ir::Width::W32));
                let a = cxt.builder.push_fun([(None, i32_ty)]);
                let b = cxt.builder.push_fun([(None, i32_ty)]);
                let val = cxt.builder.binop(op.lower(), a[0], b[0]);
                let f = cxt.builder.pop_fun(val, i32_ty);
                let fty = cxt.builder.fun_type(i32_ty, i32_ty);
                cxt.builder.pop_fun(f, fty)
            }
            Builtin::True => cxt.builder.cons(ir::Constant::Int(ir::Width::W1, 1)),
            Builtin::False => cxt.builder.cons(ir::Constant::Int(ir::Width::W1, 0)),
            Builtin::UnitType => cxt.builder.prod_type(vec![]),
            Builtin::Unit => {
                let ty = cxt.builder.prod_type(vec![]);
                cxt.builder.product(ty, vec![])
            }
            // An Eff at runtime is just the type of the effect payload
            Builtin::Eff => cxt.builder.cons(ir::Constant::TypeType),
        }
    }
}

impl<'db> LCxt<'db> {
    pub fn eff_cont_ty(&mut self, eff_ty: ir::Val, name: &str) -> ir::Val {
        // We don't actually know the return type of either continuation at the call site
        // TODO real Any type in Durin or just existential
        let any_ty = self.builder.cons(ir::Constant::TypeType);

        let rcont_ty = self.builder.fun_type_raw(&[any_ty] as &_);
        let cont_ty = self.builder.reserve(Some(format!("$ContTy.{}", name)));
        let cont_cont_ty = self
            .builder
            .fun_type_raw(&[any_ty, cont_ty, rcont_ty] as &_);
        let cont_ty2 = self.builder.fun_type_raw(&[eff_ty, cont_cont_ty] as &_);
        self.builder.redirect(cont_ty, cont_ty2);
        cont_ty
    }
}

impl Term {
    pub fn lower(&self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
        match self {
            Term::Type => cxt.builder.cons(ir::Constant::TypeType),
            Term::Lit(x, t) => x.lower(
                match t {
                    Builtin::I32 => ir::Width::W32,
                    Builtin::I64 => ir::Width::W64,
                    _ => unreachable!(),
                },
                cxt,
            ),
            Term::Var(v, _) => match v {
                Var::Builtin(b) => b.lower(cxt),
                Var::Local(i) => *cxt.locals.get(*i),
                Var::Top(i) => {
                    let (i, _, _) = cxt.db.lookup_intern_def(*i);
                    cxt.get_or_reserve(i)
                }
                Var::Rec(i) => cxt.get_or_reserve(*i),
                Var::Meta(_) => panic!("unsolved meta passed to lower()"),
                Var::Type(tid, sid) => {
                    let (pre, _, _) = cxt.db.lookup_intern_def(*tid);
                    cxt.scope_ids.insert(pre, (*tid, *sid));

                    let mut ty = ty;
                    let mut funs = Vec::new();
                    let mut targs = Vec::new();
                    loop {
                        match ty {
                            Val::Pi(_, cl) => {
                                let from = cl.ty.clone();
                                targs.push(Val::local(cxt.mcxt.size.inc(), from.clone()));

                                let lty = from.clone().lower(Val::Type, cxt);
                                let p = cxt.builder.push_fun([(None, lty.clone())]);
                                cxt.local(cl.name, p[0], from);
                                funs.push((lty, true));
                                ty = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                            }
                            Val::Fun(_, _) => unreachable!("Datatypes must have pi types"),
                            _ => break,
                        }
                    }
                    let (conses, _) = lower_datatype(*tid, *sid, targs, cxt);
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
                    let (tid, sid, base_ty) = match ty
                        .clone()
                        .ret_type(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                        .unarc()
                    {
                        Val::App(Var::Type(tid, sid), _, _, _) => (*tid, *sid, None),
                        Val::App(Var::Rec(id), _, _, _) => cxt
                            .scope_ids
                            .get(id)
                            .map(|&(a, b)| (a, b, None))
                            .expect("Datatypes should be lowered before their constructors"),
                        Val::With(base, t) => match &t[0] {
                            Val::App(Var::Type(tid, sid), _, _, _) => {
                                (*tid, *sid, Some(base.clone()))
                            }
                            Val::App(Var::Rec(id), _, _, _) => cxt
                                .scope_ids
                                .get(id)
                                .map(|&(a, b)| (a, b, Some(base.clone())))
                                .expect("Datatypes should be lowered before their constructors"),
                            x => unreachable!("{:?}", x),
                        },
                        x => unreachable!("{:?}", x),
                    };

                    // TODO should this Durin-function-from-Pika-type be its own function?
                    let mut ty = ty;
                    let mut funs = Vec::new();
                    let eff_cont = loop {
                        match ty {
                            Val::Pi(_, cl) => {
                                let from = cl.ty.clone();
                                let lty = from.clone().lower(Val::Type, cxt);

                                let name = cl.name;
                                let to = cl.vquote(cxt.mcxt.size.inc(), &cxt.mcxt, cxt.db);
                                match to {
                                    Val::With(to, mut effs) => {
                                        assert_eq!(effs.len(), 1);
                                        let eff = effs.pop().unwrap();

                                        let ename = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                                        let leff =
                                            eff.lower(Val::builtin(Builtin::Eff, Val::Type), cxt);
                                        let cont_ty = cxt.eff_cont_ty(leff, &ename);

                                        ty = *to;
                                        let p = cxt.builder.push_fun([
                                            (None, lty),
                                            (Some(format!("$cont.{}", ename)), cont_ty),
                                        ]);
                                        cxt.local(name, p[0], from);
                                        funs.push((p[0], ty.clone().lower(Val::Type, cxt), false));
                                        break Some((p[1], cont_ty));
                                    }
                                    to => {
                                        ty = to;
                                        let p = cxt.builder.push_fun([(None, lty)]);
                                        cxt.local(name, p[0], from);
                                        funs.push((p[0], ty.clone().lower(Val::Type, cxt), true));
                                    }
                                }
                            }
                            Val::Fun(from, to) => {
                                let from = from.lower(Val::Type, cxt);
                                match *to {
                                    Val::With(to, mut effs) => {
                                        assert_eq!(effs.len(), 1);
                                        let eff = effs.pop().unwrap();

                                        let name = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                                        let leff =
                                            eff.lower(Val::builtin(Builtin::Eff, Val::Type), cxt);
                                        let cont_ty = cxt.eff_cont_ty(leff, &name);

                                        ty = *to;
                                        let p = cxt.builder.push_fun([
                                            (None, from),
                                            (Some(format!("$cont.{}", name)), cont_ty),
                                        ]);
                                        funs.push((p[0], ty.clone().lower(Val::Type, cxt), false));
                                        break Some((p[1], cont_ty));
                                    }
                                    to => {
                                        ty = to;
                                        let p = cxt.builder.push_fun([(None, from)]);
                                        funs.push((p[0], ty.clone().lower(Val::Type, cxt), false));
                                    }
                                }
                            }
                            _ => break None,
                        }
                    };

                    let targs: Vec<_> = match ty {
                        Val::App(_, _, sp, _) => sp.into_iter().map(|(_i, x)| x).collect(),

                        Val::With(_, mut t) => match t.pop().unwrap() {
                            Val::App(_, _, sp, _) => sp.into_iter().map(|(_i, x)| x).collect(),
                            _ => unreachable!(),
                        },

                        _ => unreachable!(),
                    };
                    let (conses, keep) = lower_datatype(tid, sid, targs, cxt);
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

                    let prod_ty = conses[idx];
                    let sum_ty = cxt.builder.sum_type(conses);

                    let val = cxt.builder.product(
                        prod_ty,
                        funs.iter()
                            .map(|&(x, _, _)| x)
                            .zip(&keep[idx])
                            .filter_map(|(x, &b)| if b { Some(x) } else { None })
                            .collect::<SmallVec<[ir::Val; 3]>>(),
                    );
                    let mut val = cxt.builder.inject_sum(sum_ty, idx, val);

                    if let Some(base_ty) = base_ty {
                        // Pack it into a free monad and pass it to the effect continuation
                        let base_ty = base_ty.lower(Val::Type, cxt);

                        let (eff_cont, eff_cont_ty) = eff_cont.unwrap();
                        // TODO real Any type in Durin or just existential
                        let any_ty = cxt.builder.cons(ir::Constant::TypeType);
                        let rcont_ty = cxt.builder.fun_type_raw(&[any_ty] as &_);
                        let rets = cxt.builder.call_multi(
                            eff_cont,
                            &[val] as &_,
                            &[base_ty, eff_cont_ty, rcont_ty],
                        );

                        let (_p, _ty, is_pi) = funs.pop().expect(
                            "Effect constructors with no parameters not supported right now!",
                        );
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun_multi(
                            rets.into_iter()
                                .zip(vec![base_ty, eff_cont_ty, rcont_ty])
                                .collect(),
                        );
                    }

                    for (_p, ty, is_pi) in funs.into_iter().rev() {
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun(val, ty);
                    }

                    val
                }
            },
            Term::Do(sc) => {
                // Declare all the terms first
                for (id, _term) in sc {
                    let (pre_id, _cxt, _) = cxt.db.lookup_intern_def(*id);
                    let predef = cxt.db.lookup_intern_predef(pre_id);
                    let v = cxt
                        .builder
                        .reserve(predef.name().map(|n| cxt.db.lookup_intern_name(n)));
                    cxt.defs.insert(pre_id, v);
                }
                // Now lower them all
                for (id, term) in &sc[0..sc.len() - 1] {
                    let (pre_id, _cxt, _) = cxt.db.lookup_intern_def(*id);

                    let ty = cxt.db.def_type(*id).unwrap();

                    let val = term.lower((*ty).clone(), cxt);

                    let val2 = cxt.get_or_reserve(pre_id);
                    cxt.builder.redirect(val2, val);

                    lower_children(*id, cxt);
                }
                // And return the last one
                if let Some((id, term)) = sc.last() {
                    let (pre_id, _cxt, _) = cxt.db.lookup_intern_def(*id);

                    let ty = cxt.db.def_type(*id).unwrap();

                    let val = term.lower((*ty).clone(), cxt);

                    let val2 = cxt.get_or_reserve(pre_id);
                    cxt.builder.redirect(val2, val);
                    val2
                } else {
                    unreachable!("Empty do block in lower()!")
                }
            }
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
                let mut params = vec![(
                    Some(cxt.db.lookup_intern_name(*name)),
                    param_ty.clone().lower(Val::Type, cxt),
                )];
                cxt.mcxt.eff_stack.push_scope(false);
                let mut effs = Vec::new();
                let mut rcont_was_none = false;
                let mut has_eff = false;

                let ret_ty = match ret_ty {
                    Term::With(ty, effs_) => {
                        has_eff = true;
                        let mut env = cxt.mcxt.env();
                        env.push(None);
                        for eff in effs_ {
                            let leff = eff.lower(Val::builtin(Builtin::Eff, Val::Type), cxt);
                            let eff = eff.evaluate(&env, &cxt.mcxt, cxt.db);
                            let name = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                            let cont_ty = cxt.eff_cont_ty(leff, &name);
                            effs.push(eff);
                            params.push((Some(format!("$cont.{}", name)), cont_ty))
                        }
                        *ty
                    }
                    ty => ty,
                };
                let args = cxt.builder.push_fun(params);
                if has_eff && cxt.rcont.is_none() {
                    cxt.rcont = cxt.builder.cont();
                    rcont_was_none = true;
                }
                cxt.local(*name, args[0], param_ty);
                for (k, e) in args.into_iter().skip(1).zip(effs) {
                    cxt.eff(e, k);
                }
                let ret = body.lower(
                    ret_ty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db),
                    cxt,
                );
                let ret_ty = ret_ty.lower(Val::Type, cxt);

                let val = if has_eff {
                    let mut rets = vec![(ret, ret_ty)];
                    let any_ty = cxt.builder.cons(ir::Constant::TypeType);
                    for &k in &cxt.eff_conts[cxt.mcxt.eff_stack.scope_start().unwrap()..] {
                        rets.push((k, cxt.builder.fun_type_raw(&[any_ty, any_ty, any_ty] as &_)));
                    }
                    rets.push((
                        cxt.rcont.unwrap(),
                        cxt.builder.fun_type_raw(&[any_ty] as &_),
                    ));
                    cxt.builder.pop_fun_multi(rets)
                } else {
                    cxt.builder.pop_fun(ret, ret_ty)
                };
                if rcont_was_none {
                    cxt.rcont = None;
                }
                cxt.mcxt.eff_stack.pop_scope();
                cxt.pop_local();
                val
            }
            Term::App(_icit, f, fty, x) => {
                let ret_ty = ty;
                let ret_ty = ret_ty.lower(Val::Type, cxt);
                let fty = fty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db);
                let (xty, rty) = match fty.unarc() {
                    Val::Pi(_, cl) => (
                        cl.ty.clone(),
                        cl.clone().vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db),
                    ),
                    Val::Fun(x, y) => ((**x).clone(), (**y).unarc().clone()),
                    _ => unreachable!(),
                };
                let f = f.lower(fty, cxt);
                let x = x.lower(xty, cxt);
                match rty {
                    Val::With(rty, effs) => {
                        let mut args = vec![x];
                        let mut rets = vec![rty.lower(Val::Type, cxt)];
                        let mut is = Vec::new();
                        let mut tcxt = cxt.mcxt.clone();
                        for eff in effs {
                            let i = cxt
                                .mcxt
                                .eff_stack
                                .find_eff(&eff, cxt.db, &mut tcxt)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Could not find effect {:?} in context {:?}",
                                        eff, cxt.mcxt.eff_stack
                                    )
                                });
                            args.push(cxt.eff_conts[i]);
                            let name = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                            let leff = eff.lower(Val::builtin(Builtin::Eff, Val::Type), cxt);
                            rets.push(cxt.eff_cont_ty(leff, &name));
                            is.push(i);
                        }
                        let any_ty = cxt.builder.cons(ir::Constant::TypeType);
                        rets.push(cxt.builder.fun_type_raw(&[any_ty] as &_));
                        let rets = cxt.builder.call_multi(f, args, &rets);
                        for (k, i) in rets.iter().skip(1).zip(is) {
                            cxt.eff_conts[i] = *k;
                        }
                        cxt.rcont = Some(*rets.last().unwrap());
                        rets[0]
                    }
                    _ => cxt.builder.call(f, vec![x], ret_ty),
                }
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
            Term::Case(x, xty, cases) => {
                let xty = (**xty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db);
                let x = x.lower(xty, cxt);

                let cont = cases
                    .iter()
                    .rfold(PatCont::Unreachable, |rest, (pat, term)| PatCont::Pat {
                        x,
                        pat,
                        cont: Box::new(PatCont::Term(term)),
                        rest: Box::new(rest),
                    });
                cont.lower(ty, cxt)
            }
            Term::If(cond, yes, no) => {
                let cond = cond.lower(Val::builtin(Builtin::Bool, Val::Type), cxt);
                cxt.if_expr(cond);

                let yes = yes.lower(ty.clone(), cxt);
                cxt.otherwise(yes);

                let no = no.lower(ty.clone(), cxt);
                let lty = ty.lower(Val::Type, cxt);
                cxt.endif(no, lty)
            }
            Term::With(base, effs) => {
                let base = base.lower(Val::Type, cxt);

                let mut v = vec![base];
                for e in effs {
                    // TODO include continuation
                    let e = e.lower(Val::builtin(Builtin::Eff, Val::Type), cxt);
                    v.push(e);
                }
                cxt.builder.sum_type(v)
            }
        }
    }
}

#[derive(Clone, Debug)]
enum PatCont<'a> {
    Unreachable,
    Term(&'a Term),
    Pat {
        x: ir::Val,
        pat: &'a Pat,
        cont: Box<PatCont<'a>>,
        rest: Box<PatCont<'a>>,
    },
}
impl<'a> PatCont<'a> {
    fn lower(&'a self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
        match self {
            PatCont::Unreachable => {
                let ty = ty.lower(Val::Type, cxt);
                cxt.builder.unreachable(ty)
            }
            PatCont::Term(x) => x.lower(ty, cxt),
            PatCont::Pat { x, pat, cont, rest } => pat.lower(*x, &cont, &rest, ty, cxt),
        }
    }
}

impl Literal {
    fn lower(self, w: ir::Width, cxt: &mut LCxt) -> ir::Val {
        match self {
            Literal::Positive(i) => cxt.builder.cons(ir::Constant::Int(w, i as i64)),
            Literal::Negative(i) => cxt.builder.cons(ir::Constant::Int(w, i)),
        }
    }
}

impl Pat {
    fn lower<'a>(
        &'a self,
        x: ir::Val,
        cont: &'a PatCont<'a>,
        rest: &'a PatCont<'a>,
        ty: VTy,
        cxt: &mut LCxt,
    ) -> ir::Val {
        match self {
            Pat::Any => cont.lower(ty, cxt),
            Pat::Var(n, vty) => {
                cxt.local(*n, x, (**vty).clone());
                let ret = cont.lower(ty, cxt);
                cxt.pop_local();
                ret
            }
            Pat::Lit(l, w) => {
                let l = l.lower(*w, cxt);
                let eq = cxt.builder.binop(ir::BinOp::IEq, l, x);
                cxt.if_expr(eq);

                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                let lty = ty.clone().lower(Val::Type, cxt);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
            }
            Pat::Bool(b) => {
                let l = cxt
                    .builder
                    .cons(ir::Constant::Int(ir::Width::W1, *b as i64));
                let eq = cxt.builder.binop(ir::BinOp::IEq, l, x);
                cxt.if_expr(eq);

                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                let lty = ty.clone().lower(Val::Type, cxt);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
            }
            Pat::Cons(id, xty, args) => {
                let (tid, sid, targs) = match xty.unarc() {
                    Val::App(Var::Type(tid, sid), _, sp, _) => {
                        (*tid, *sid, sp.iter().map(|(_, v)| v.clone()).collect())
                    }
                    Val::App(Var::Rec(id), _, sp, _) => cxt
                        .scope_ids
                        .get(id)
                        .map(|&(x, y)| (x, y, sp.iter().map(|(_, v)| v.clone()).collect()))
                        .expect("Datatypes should be lowered before their constructors"),
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

                let (ltys, _) = lower_datatype(tid, sid, targs, cxt);
                let lty = ltys[idx];
                let product = cxt.ifcase(idx, x, lty);

                let cont = args
                    .iter()
                    .enumerate()
                    .fold(cont.clone(), |cont, (i, pat)| {
                        let x = cxt.builder.project(product, i);
                        PatCont::Pat {
                            x,
                            pat,
                            cont: Box::new(cont),
                            rest: Box::new(rest.clone()),
                        }
                    });
                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                let lty = ty.clone().lower(Val::Type, cxt);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
            }
            Pat::Or(a, b) => {
                let rest = PatCont::Pat {
                    x,
                    pat: b,
                    cont: Box::new(cont.clone()),
                    rest: Box::new(rest.clone()),
                };
                a.lower(x, cont, &rest, ty, cxt)
            }
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
