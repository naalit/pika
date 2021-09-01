//! This module deals with translation to Durin.

use crate::elaborate::{MCxt, MCxtType};
use crate::error::FileId;
use crate::term::*;
use crate::{common::*, pattern::Pat};
use durin::ir;
use durin::{builder::*, ir::Float};

use smallvec::SmallVec;
use std::collections::HashMap;

pub struct ModCxt<'m> {
    db: &'m dyn Compiler,
    defs: HashMap<PreDefId, ir::Val>,
    scope_ids: HashMap<PreDefId, (DefId, ScopeId)>,
    module: ir::Module,
    entry: Option<ir::Val>,
    state: Option<BuildState>,
}
impl<'m> ModCxt<'m> {
    pub fn finish(mut self, main: Option<ir::Val>) -> ir::Module {
        use durin::ir::{Slots, WorldExt};

        if let Some(main) = main {
            let mut is_valid = true;
            match self.module.slots().node(main) {
                Some(ir::Node::Fun(f)) => {
                    is_valid &= f.params.len() == 2;
                    is_valid &= matches!(self.module.slots().node(f.params[0]), Some(ir::Node::ProdType(v)) if v.is_empty());
                    is_valid &= matches!(
                        self.module.slots().node(f.params[1]),
                        Some(ir::Node::FunType(1))
                    );
                }
                _ => is_valid = false,
            }
            if !is_valid {
                Doc::start("error")
                    .style(Style::BoldRed)
                    .add(": `main` function must have type ")
                    .style(Style::Bold)
                    .chain(Doc::start("() -> ()").chain(Doc::keyword("with").add("IO")))
                    .emit();
                std::process::exit(1);
            }

            let mut builder = Builder::new(&mut self.module, self.state);
            let unit_ty = builder.prod_type(&[] as &_);
            let unit = builder.product(unit_ty, &[] as &_);
            builder.call(main, &[unit] as &_, unit_ty);
            builder.stop();
        } else {
            Builder::new(&mut self.module, self.state).stop();
        }
        self.module
            .world
            .write_component()
            .insert(self.entry.unwrap(), ir::Name("$__entry".to_string()))
            .unwrap();
        self.module
    }

    pub fn new(db: &'m dyn Compiler) -> Self {
        ModCxt {
            db,
            defs: HashMap::new(),
            scope_ids: HashMap::new(),
            module: ir::Module::new(),
            entry: None,
            state: None,
        }
    }

    pub fn local(&mut self, def: DefId, f: impl FnOnce(&mut LCxt) -> ir::Val) {
        let (pre, state) = self.db.lookup_intern_def(def);
        let locals = IVec::new();
        let mut lcxt = LCxt::new(
            self.db,
            MCxt::from_state(state, MCxtType::Local(def), self.db),
            &mut self.module,
            &mut self.defs,
            &mut self.scope_ids,
            locals,
            self.state.clone(),
        );
        if self.entry.is_none() {
            self.entry = Some(lcxt.builder.state().block);
        }
        let val = f(&mut lcxt);
        self.state = Some(lcxt.builder.state());

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
    mcxt: MCxt<'db>,
    eff_conts: Vec<ir::Val>,
}
impl<'db> LCxt<'db> {
    fn new(
        db: &'db dyn Compiler,
        mcxt: MCxt<'db>,
        m: &'db mut ir::Module,
        defs: &'db mut HashMap<PreDefId, ir::Val>,
        scope_ids: &'db mut HashMap<PreDefId, (DefId, ScopeId)>,
        locals: IVec<ir::Val>,
        state: Option<BuildState>,
    ) -> Self {
        let builder = Builder::new(m, state);
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
        self.mcxt.define(name, NameInfo::Local(ty));
    }

    pub fn pop_local(&mut self) {
        self.locals.remove();
        self.mcxt.undef();
    }

    pub fn trunc_locals(&mut self, to_size: Size) {
        while self.mcxt.size != to_size {
            self.pop_local();
        }
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
            rets.push((k, self.builder.fun_type(1)));
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

/// Effects example:
/// ```pika
/// eff Console of
///     Read () : I32
///     Print I32 : ()
/// end
///
/// fun other () = catch Print 3 of
///     () => ()
///     eff (Print i) k => k ()
///     eff (Read ()) k => k 12
/// end
///
/// # -->
///
/// val Console = ({} | { I32 });
///
/// fun Print (x : I32, kPrint : fun 2, kRet : fun 1) = kPrint (Console:1 {x}) Print2;
/// fun Print2 (_ : {}) = kRet {};
///
/// fun other (_ : {}, kRet : fun 1) = refnew fun 1 o2;
//  fun o2 (r : ref fun 1) = refset r kRet o3;
//  fun o3 () = Print 3 oP oR;
/// fun oP (x : Console, k : fun 2) = ifcase 0 x oP0 oP_;
/// fun oP0 (_ : {}) = k 12 kRet;
/// fun oP_ () = ifcase 1 x oP1 unreachable;
/// fun oP1 (i : { I32 }) = k {} kRet;
/// fun oR (_ : {}) = refget r oR2;
//  fun oR2 (f : fun 1) = f {};
/// ```
impl<'db> LCxt<'db> {
    fn raise_effect(&mut self, eff_cont: ir::Val, eff_val: ir::Val, ret_ty: ir::Val) -> ir::Val {
        self.builder.call(eff_cont, &[eff_val] as &[_], ret_ty)
    }

    fn catch(
        &mut self,
        effs: &[Val],
        pure_ty: Val,
        ret_ty: ir::Val,
        term: &Term,
        mut do_eff: impl FnMut(&mut Self, usize, ir::Val, ir::Val) -> ir::Val,
        do_pure: impl FnOnce(&mut Self, ir::Val) -> ir::Val,
    ) -> ir::Val {
        // There are four types of continuation used here, so here are some consistent names:
        // 1. *Effect continuations* are the things that are called directly by raising an effect.
        //    They contain the body of one of the `eff` branches of the `catch`.
        // 2. The *pure continuation* is called when the term finishes and returns a value.
        //    It contains the non-`eff` branches of the `catch`.
        // 3. The continuation created by raising and passed to the effect continuation,
        //    the only one reified in Pika code, is the *resume continuation*.
        // 4. When they're done, the effect continuations and the pure continuation both
        //    have to call another continuation, since they don't know where to return their value to.
        //    That continuation is called the *return continuation*, and it's inside a `ref`
        //    which is updated with the function return continuation of the resume continuation.

        let ret_cont_ty = self.builder.fun_type(1);
        let ret_cont = self.builder.refnew(ret_cont_ty);
        let ret_cont_start = self.builder.reserve(None);
        self.builder.refset(ret_cont, ret_cont_start);

        let mut conts = Vec::new();
        for (i, eff) in effs.iter().enumerate() {
            let leff = eff.clone().lower(self);
            let args = [(None, leff), (None, self.builder.fun_type(1))];
            let v = self.builder.push_fun_raw(args);
            let eff_val = v[0];
            let resume = v[1];

            let resume_wrapper = {
                let any_ty = self.builder.ref_type(ret_cont_ty);
                let args = [(None, any_ty), (None, self.builder.fun_type(1))];
                let v = self.builder.push_fun_raw(args);
                let val = v[0];
                let new_ret_cont = v[1];
                self.builder.refset(ret_cont, new_ret_cont);
                self.builder.pop_fun_raw(resume, &[val] as &[_])
            };

            let ret_cont = self.builder.refget(ret_cont);
            let val = do_eff(self, i, eff_val, resume_wrapper);

            let econt = self.builder.pop_fun_raw(ret_cont, &[val] as &[_]);
            conts.push((eff.clone(), econt));
        }

        let pure_cont = {
            let lpure_ty = pure_ty.lower(self);
            let v = self.builder.push_fun_raw([(None, lpure_ty)]);
            let pure_val = v[0];
            let pure_ret = do_pure(self, pure_val);
            let ret_cont = self.builder.refget(ret_cont);
            self.builder.pop_fun_raw(ret_cont, &[pure_ret] as &[_])
        };

        for (val, cont) in conts {
            self.eff(val, cont);
        }

        let pure_val = term.lower(self);
        self.builder.call_raw(pure_cont, &[pure_val] as &[_]);
        let (cont, v) = self.builder.push_frame(vec![(ret_cont_start, ret_ty)]);
        self.builder.redirect(ret_cont_start, cont);
        v[0]
    }
}

impl Val {
    /// Assuming this is the type of a constructor, returns `(type ID, scope ID, base type if this is an effect constructor)`
    pub fn cons_parent(self, at: Size, cxt: &LCxt) -> (DefId, ScopeId, Option<Val>) {
        match self {
            Val::App(Var::Type(tid, sid), _, _, _) => (tid, sid, None),
            Val::App(Var::Rec(id), _, _, _) => cxt
                .scope_ids
                .get(&id)
                .map(|&(a, b)| (a, b, None))
                .expect("Datatypes should be lowered before their constructors"),
            Val::Fun(_, to, effs) if effs.is_empty() => to.cons_parent(at, cxt),
            Val::Fun(_, to, mut effs) => {
                assert_eq!(effs.len(), 1);
                let (tid, sid, _) = effs.pop().unwrap().cons_parent(at, cxt);
                (tid, sid, Some(*to))
            }
            Val::Clos(Pi, _, cl, effs) if effs.is_empty() => {
                cl.vquote(at, &cxt.mcxt).cons_parent(at.inc(), cxt)
            }
            Val::Clos(Pi, _, cl, mut effs) => {
                assert_eq!(effs.len(), 1);
                let (tid, sid, _) = effs.pop().unwrap().cons_parent(at, cxt);
                let to = cl.vquote(at, &cxt.mcxt);
                (tid, sid, Some(to))
            }
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).cons_parent(at, cxt),
            x => unreachable!("{:?}", x),
        }
    }

    pub fn lower(self, cxt: &mut LCxt) -> ir::Val {
        // If this is a datatype applied to all its arguments, inline the sum type
        // That way Durin knows the type when calling ifcase
        let (tid, sid, targs) = match self {
            Val::App(Var::Type(tid, sid), _, sp, _) => (
                tid,
                sid,
                sp.into_iter().map(|e| e.into_app().unwrap().1).collect(),
            ),
            Val::App(Var::Top(tid), hty, sp, g) => {
                if let Some(&(x, y)) = cxt.scope_ids.get(&cxt.db.lookup_intern_def(tid).0) {
                    (
                        x,
                        y,
                        sp.into_iter().map(|e| e.into_app().unwrap().1).collect(),
                    )
                } else {
                    return Val::App(Var::Top(tid), hty, sp, g)
                        .quote(cxt.mcxt.size, &cxt.mcxt)
                        .lower(cxt);
                }
            }
            Val::App(Var::Rec(id), hty, sp, g) => {
                if let Some(&(x, y)) = cxt.scope_ids.get(&id) {
                    (
                        x,
                        y,
                        sp.into_iter().map(|e| e.into_app().unwrap().1).collect(),
                    )
                } else {
                    return Val::App(Var::Rec(id), hty, sp, g)
                        .quote(cxt.mcxt.size, &cxt.mcxt)
                        .lower(cxt);
                }
            }
            Val::Arc(x) => return IntoOwned::<Val>::into_owned(x).lower(cxt),
            x => return x.quote(cxt.mcxt.size, &cxt.mcxt).lower(cxt),
        };
        let (tys, _) = lower_datatype(tid, sid, targs, cxt);
        cxt.builder.sum_type(tys)
    }
}

pub fn durin(db: &dyn Compiler, files: impl IntoIterator<Item = FileId>) -> ir::Module {
    let mut mcxt = ModCxt::new(db);
    let mut solved_globals = db.check_all();
    let mut main = None;
    for file in files {
        for &def in &*db.top_level(file) {
            if let Ok(info) = db.elaborate_def(def) {
                mcxt.local(def, |lcxt| {
                    std::mem::swap(&mut solved_globals, &mut lcxt.mcxt.solved_globals);
                    let val = info.term.as_ref().unwrap().lower(lcxt);
                    lower_children(def, lcxt);
                    std::mem::swap(&mut solved_globals, &mut lcxt.mcxt.solved_globals);

                    let (pre, _) = db.lookup_intern_def(def);
                    let pre = db.lookup_intern_predef(pre);
                    let name = pre.name();
                    if name.map_or(false, |n| db.lookup_intern_name(n) == "main") {
                        if main.is_some() {
                            eprintln!(
                                "Warning: more than one `main` functions, picking the first one"
                            );
                        } else {
                            main = Some(val);
                        }
                    }

                    val
                });
            }
        }
    }
    mcxt.finish(main)
}

fn lower_children(def: DefId, cxt: &mut LCxt) {
    let mut stack = match cxt.db.elaborate_def(def) {
        Ok(info) => (*info.children).clone(),
        _ => return,
    };
    while let Some(def) = stack.pop() {
        if let Ok(info) = cxt.db.elaborate_def(def) {
            let (pre_id, _state) = cxt.db.lookup_intern_def(def);
            let val = info.term.as_ref().unwrap().lower(cxt);
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
            match &**info.term.as_ref().unwrap() {
                Term::Var(Var::Cons(cid), _) if id == *cid => {
                    let mut cty: Val = info.typ.into_owned();
                    let solutions = {
                        let start_state = cxt.mcxt.state();

                        // First define the locals from the type
                        let mut tty: Val = cxt.db.elaborate_def(tid).unwrap().typ.into_owned();
                        let mut ty_args = Vec::new();
                        loop {
                            match tty {
                                Val::Clos(Pi, i, cl, _) => {
                                    let from = cl.ty.clone();
                                    ty_args.push(Elim::App(
                                        i,
                                        Val::local(cxt.mcxt.size.next_lvl(), from.clone()),
                                    ));
                                    cxt.mcxt.define(cl.name, NameInfo::Local(from));
                                    tty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt);
                                }
                                Val::Fun(_, _, _) => unreachable!("Datatypes must have pi types"),
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
                            .quote(cxt.mcxt.size, &cxt.mcxt)
                            .evaluate(&cxt.mcxt.env(), &cxt.mcxt);
                        loop {
                            match cty {
                                Val::Clos(Pi, _, cl, mut effs) => {
                                    let from = cl.ty.clone();
                                    cxt.mcxt.define(cl.name, NameInfo::Local(from.clone()));
                                    if effs.is_empty() {
                                        cty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt);
                                    } else {
                                        assert_eq!(effs.len(), 1);
                                        cty = effs.pop().unwrap();
                                        break;
                                    }
                                }
                                Val::Fun(_from, to, mut effs) => {
                                    // This argument can't be used in the type, so we skip it
                                    if effs.is_empty() {
                                        cty = *to;
                                    } else {
                                        assert_eq!(effs.len(), 1);
                                        cty = effs.pop().unwrap();
                                        break;
                                    }
                                }
                                _ => break,
                            }
                        }

                        // Now unify
                        let mut tcxt = cxt.mcxt.clone();
                        if !crate::elaborate::local_unify(
                            tty,
                            cty,
                            cxt.mcxt.size,
                            Span::empty(),
                            &mut tcxt,
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
                        let mut size = lbefore;
                        let mut solutions: Vec<Option<Val>> = Vec::new();
                        while size <= tcxt.size {
                            if let Some(v) = tcxt.local_val(size.next_lvl()) {
                                let v = v.clone().quote(env.size, &tcxt).evaluate(&env, &tcxt);
                                solutions.push(Some(v));
                            } else {
                                solutions.push(None);
                            }
                            size = size.inc();
                        }
                        cxt.mcxt.set_state(start_state);
                        solutions
                    };

                    // Now generate the sigma type representing the constructor
                    let mut i = 0;
                    let mut prod = Vec::new();
                    let mut keep = Vec::new();
                    let mut env = Env::new(cxt.mcxt.size);
                    loop {
                        assert_eq!(env.size, cxt.mcxt.size);
                        match cty {
                            Val::Clos(Pi, _, cl, effs) => {
                                // Quote-evaluate to apply substitutions from the environment
                                let from = cl
                                    .ty
                                    .clone()
                                    .quote(env.size, &cxt.mcxt)
                                    .evaluate(&env, &cxt.mcxt);

                                // [a] -> (_:a) -> Option a
                                let val = if let Some(x) = &solutions[i] {
                                    // TODO: don't add the parameter to the sigma, but keep it around in some form for pattern matching
                                    // Right now, we have to add it even if it's solved, since code can pattern match on it

                                    // keep.push(false);
                                    keep.push(true);
                                    // Add the solution to the environment
                                    env.push(Some(x.clone()));
                                    // If we solved it, skip adding it to the sigma
                                    // This shouldn't be used at all
                                    prod.push(from.clone().lower(cxt));
                                    cxt.builder.cons(ir::Constant::BoxTy)
                                } else {
                                    // It doesn't have a solution, so it remains in the product type
                                    keep.push(true);
                                    env.push(None);
                                    prod.push(from.clone().lower(cxt));
                                    cxt.builder.cons(ir::Constant::BoxTy)
                                };

                                // Define the variable and go to the next level
                                cxt.local(cl.name, val, from);
                                cty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt);
                                i += 1;
                                if !effs.is_empty() {
                                    break;
                                }
                            }
                            Val::Fun(from, to, effs) => {
                                // Quote-evaluate to apply substitutions from the environment
                                let from =
                                    from.quote(env.size, &cxt.mcxt).evaluate(&env, &cxt.mcxt);

                                // We know we're keeping this one, since we can't solve a non-pi parameter
                                keep.push(true);

                                // Don't add the parameter to the context, since it's not a pi
                                prod.push(from.clone().lower(cxt));
                                cty = *to;
                                if !effs.is_empty() {
                                    break;
                                }
                            }
                            _ => break,
                        }
                    }
                    for _ in 0..i {
                        cxt.pop_local();
                    }
                    Some((cxt.builder.prod_type(prod), keep))
                }
                _ => None,
            }
        })
        .unzip()
}

impl BinOp {
    fn lower(self) -> ir::BinOp {
        match self {
            BinOp::Add => ir::BinOp::Add,
            BinOp::Sub => ir::BinOp::Sub,
            BinOp::Mul => ir::BinOp::Mul,
            BinOp::Div => ir::BinOp::Div,
            BinOp::Exp => ir::BinOp::Pow,
            BinOp::Mod => ir::BinOp::Mod,
            BinOp::BitAnd => ir::BinOp::And,
            BinOp::BitOr => ir::BinOp::Or,
            BinOp::BitXor => ir::BinOp::Xor,
            BinOp::BitShl => ir::BinOp::Shl,
            BinOp::BitShr => ir::BinOp::Shr,

            BinOp::Eq => ir::BinOp::Eq,
            BinOp::NEq => ir::BinOp::NEq,
            BinOp::Lt => ir::BinOp::Lt,
            BinOp::Gt => ir::BinOp::Gt,
            BinOp::Leq => ir::BinOp::Leq,
            BinOp::Geq => ir::BinOp::Geq,

            _ => todo!("lower pipes"),
        }
    }
}

impl Term {
    fn binop_ty(&self, cxt: &mut LCxt) -> (ir::Val, bool) {
        match self {
            Term::Fun(ity, _, _) => {
                let signed = match &**ity {
                    Term::Var(Var::Builtin(Builtin::I32), _)
                    | Term::Var(Var::Builtin(Builtin::I64), _)
                    | Term::Var(Var::Builtin(Builtin::F32), _)
                    | Term::Var(Var::Builtin(Builtin::F64), _) => true,
                    _ => unreachable!(),
                };
                ((**ity).clone().lower(cxt), signed)
            }
            _ => unreachable!(),
        }
    }
}

impl Builtin {
    fn lower(self, ty: &Ty, cxt: &mut LCxt) -> ir::Val {
        match self {
            Builtin::I32 => cxt.builder.cons(ir::Constant::IntType(ir::Width::W32)),
            Builtin::I64 => cxt.builder.cons(ir::Constant::IntType(ir::Width::W64)),
            Builtin::F32 => cxt
                .builder
                .cons(ir::Constant::FloatType(ir::FloatType::F32)),
            Builtin::F64 => cxt
                .builder
                .cons(ir::Constant::FloatType(ir::FloatType::F64)),
            Builtin::String => cxt.builder.cons(ir::Constant::StringTy),
            // Bool translates to i1
            Builtin::Bool => cxt.builder.cons(ir::Constant::IntType(ir::Width::W1)),
            Builtin::BinOp(op) => {
                let (ity, signed) = ty.binop_ty(cxt);
                let a = cxt.builder.push_fun([(None, ity)]);
                let b = cxt.builder.push_fun([(None, ity)]);
                let val = cxt.builder.binop(op.lower(), signed, a[0], b[0]);
                let f = cxt.builder.pop_fun(val);
                cxt.builder.pop_fun(f)
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
            Builtin::IO => panic!("IO effects should disappear before this stage!"),
            Builtin::Print => {
                let i32_ty = cxt.builder.cons(ir::Constant::IntType(ir::Width::W32));
                let void_ty = cxt.builder.prod_type(vec![]);
                let extern_fun =
                    cxt.builder
                        .extern_declare("print_i32".into(), &[i32_ty] as &_, void_ty);
                let x = cxt.builder.push_fun([(None, i32_ty)]);
                let r = cxt.builder.extern_call(extern_fun, x);
                cxt.builder.pop_fun(r)
            }
            Builtin::Puts => {
                let str_ty = cxt.builder.cons(ir::Constant::StringTy);
                let void_ty = cxt.builder.prod_type(vec![]);
                let extern_fun =
                    cxt.builder
                        .extern_declare("print_str".into(), &[str_ty] as &_, void_ty);
                let x = cxt.builder.push_fun([(None, str_ty)]);
                let r = cxt.builder.extern_call(extern_fun, x);
                cxt.builder.pop_fun(r)
            }
        }
    }
}

impl Term {
    pub fn lower(&self, cxt: &mut LCxt) -> ir::Val {
        match self {
            Term::Type => cxt.builder.cons(ir::Constant::TypeType),
            Term::Lit(x, t) => x.lower(
                match t {
                    Builtin::I32 | Builtin::F32 => ir::Width::W32,
                    Builtin::I64 | Builtin::F64 => ir::Width::W64,
                    // The width isn't used, so it doesn't matter
                    Builtin::String => ir::Width::W8,
                    _ => unreachable!(),
                },
                cxt,
            ),
            Term::Var(v, ty) => match v {
                Var::File(id) => {
                    let mut prod = Vec::new();
                    let mut tys = Vec::new();
                    for &i in &*cxt.db.top_level(*id) {
                        let ty = cxt.db.elaborate_def(i).unwrap().typ;
                        let (i, _) = cxt.db.lookup_intern_def(i);
                        let pre = cxt.db.lookup_intern_predef(i);
                        prod.push((pre.name().unwrap(), cxt.get_or_reserve(i)));
                        tys.push((pre.name().unwrap(), (*ty).clone().lower(cxt)));
                    }

                    prod.sort_by_key(|(n, _)| n.get(cxt.db));
                    let prod: SmallVec<_> = prod.into_iter().map(|(_, x)| x).collect();
                    tys.sort_by_key(|(n, _)| n.get(cxt.db));
                    let tys: SmallVec<_> = tys.into_iter().map(|(_, x)| x).collect();

                    let ty = cxt.builder.prod_type(tys);
                    cxt.builder.product(ty, prod)
                }
                Var::Builtin(b) => b.lower(&ty, cxt),
                Var::Local(i) => *cxt.locals.get(*i),
                Var::Top(i) => {
                    let (i, _) = cxt.db.lookup_intern_def(*i);
                    cxt.get_or_reserve(i)
                }
                Var::Rec(i) => cxt.get_or_reserve(*i),
                Var::Meta(m) => panic!(
                    "Compiler error: Found unsolved metavariable during lowering: {:?}",
                    m
                ),
                Var::Type(tid, sid) => {
                    let (pre, _) = cxt.db.lookup_intern_def(*tid);
                    cxt.scope_ids.insert(pre, (*tid, *sid));

                    let mut ty = (**ty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt);
                    let mut funs = Vec::new();
                    let mut targs = Vec::new();
                    loop {
                        match ty {
                            Val::Clos(Pi, _, cl, _) => {
                                let from = cl.ty.clone();
                                targs.push(Val::local(cxt.mcxt.size.next_lvl(), from.clone()));

                                let lty = from.clone().lower(cxt);
                                let p = cxt.builder.push_fun([(None, lty)]);
                                cxt.local(cl.name, p[0], from);
                                funs.push((lty, true));
                                // Make sure to vquote outside of the closure
                                ty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt);
                            }
                            Val::Fun(_, _, _) => unreachable!("Datatypes must have pi types"),
                            _ => break,
                        }
                    }
                    let (conses, _) = lower_datatype(*tid, *sid, targs, cxt);
                    let mut val = cxt.builder.sum_type(conses);
                    for (_ty, is_pi) in funs.into_iter().rev() {
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun(val);
                    }
                    val
                }
                Var::Cons(id) => {
                    let info = cxt.db.elaborate_def(*id).unwrap();
                    let ty = info.typ;
                    let (tid, sid, base_ty) = (*ty).clone().cons_parent(cxt.mcxt.size, cxt);

                    // TODO should this Durin-function-from-Pika-type be its own function?
                    let mut ty = (*ty).clone();
                    let mut funs = Vec::new();
                    let eff_cont = loop {
                        match ty {
                            Val::Clos(Pi, _, cl, mut effs) => {
                                let from = cl.ty.clone();
                                let lty = from.clone().lower(cxt);

                                let name = cl.name;
                                let to = cl.vquote(cxt.mcxt.size, &cxt.mcxt);

                                if effs.is_empty() {
                                    ty = to;
                                    let p = cxt.builder.push_fun([(None, lty)]);
                                    cxt.local(name, p[0], from);
                                    funs.push((p[0], ty.clone().lower(cxt), true));
                                } else {
                                    assert_eq!(effs.len(), 1);
                                    let eff = effs.pop().unwrap();

                                    let ename = eff.pretty(&cxt.mcxt).raw_string();
                                    let cont_ty = cxt.builder.fun_type(2);

                                    ty = eff;
                                    // The function takes a continuation for each effect, plus a return continuation
                                    let p = cxt.builder.push_fun([
                                        (None, lty),
                                        (Some(format!("$cont.{}", ename)), cont_ty),
                                    ]);
                                    cxt.local(name, p[0], from);
                                    funs.push((p[0], ty.clone().lower(cxt), true));
                                    break Some(p[1]);
                                }
                            }
                            Val::Fun(from, to, mut effs) => {
                                let from = from.lower(cxt);

                                if effs.is_empty() {
                                    ty = *to;
                                    let p = cxt.builder.push_fun([(None, from)]);
                                    funs.push((p[0], ty.clone().lower(cxt), false));
                                } else {
                                    assert_eq!(effs.len(), 1);
                                    let eff = effs.pop().unwrap();

                                    let name = eff.pretty(&cxt.mcxt).raw_string();
                                    let cont_ty = cxt.builder.fun_type(2);

                                    ty = eff;
                                    // The function takes a continuation for each effect, plus a return continuation
                                    let p = cxt.builder.push_fun([
                                        (None, from),
                                        (Some(format!("$cont.{}", name)), cont_ty),
                                    ]);
                                    funs.push((p[0], ty.clone().lower(cxt), false));
                                    break Some(p[1]);
                                }
                            }
                            _ => break None,
                        }
                    };

                    let targs: Vec<_> = match ty {
                        Val::App(_, _, sp, _) => {
                            sp.into_iter().map(|e| e.into_app().unwrap().1).collect()
                        }

                        _ => unreachable!(),
                    };
                    let (conses, keep) = lower_datatype(tid, sid, targs, cxt);
                    let idx = cxt
                        .db
                        .lookup_intern_scope(sid)
                        .iter()
                        .filter_map(|&(_name, id)| {
                            let info = cxt.db.elaborate_def(id).ok()?;
                            match &**info.term.as_ref().unwrap() {
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
                        let eff_cont = eff_cont.unwrap();
                        let base_ty = base_ty.lower(cxt);

                        let ret = cxt.raise_effect(eff_cont, val, base_ty);

                        let (_p, _ty, is_pi) = funs.pop().expect(
                            "Effect constructors with no parameters not supported right now!",
                        );
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun(ret);
                    }

                    for (_p, _ty, is_pi) in funs.into_iter().rev() {
                        if is_pi {
                            cxt.pop_local();
                        }
                        val = cxt.builder.pop_fun(val);
                    }

                    val
                }
            },
            Term::Do(sc) => {
                // Declare all the terms first
                for (id, _term) in sc {
                    let (pre_id, _state) = cxt.db.lookup_intern_def(*id);
                    let predef = cxt.db.lookup_intern_predef(pre_id);
                    let v = cxt
                        .builder
                        .reserve(predef.name().map(|n| cxt.db.lookup_intern_name(n)));
                    cxt.defs.insert(pre_id, v);
                }
                // Now lower them all
                for (id, term) in &sc[0..sc.len() - 1] {
                    let (pre_id, _state) = cxt.db.lookup_intern_def(*id);

                    let val = term.lower(cxt);

                    let val2 = cxt.get_or_reserve(pre_id);
                    cxt.builder.redirect(val2, val);

                    lower_children(*id, cxt);
                }
                // And return the last one
                if let Some((id, term)) = sc.last() {
                    let (pre_id, _state) = cxt.db.lookup_intern_def(*id);

                    let val = term.lower(cxt);

                    let val2 = cxt.get_or_reserve(pre_id);
                    cxt.builder.redirect(val2, val);
                    val2
                } else {
                    unreachable!("Empty do block in lower()!")
                }
            }
            Term::Box(true, _) => cxt.builder.cons(ir::Constant::BoxTy),
            Term::Box(false, x) => {
                let x = x.lower(cxt);
                cxt.builder.unbox(x)
            }
            Term::Struct(StructKind::Struct(t), v) => {
                let t = t.lower(cxt);

                let mut prod = Vec::new();
                // Declare all the terms first
                for (id, _, _term) in v {
                    let (pre_id, _state) = cxt.db.lookup_intern_def(*id);
                    let predef = cxt.db.lookup_intern_predef(pre_id);
                    let v = cxt
                        .builder
                        .reserve(predef.name().map(|n| cxt.db.lookup_intern_name(n)));
                    cxt.defs.insert(pre_id, v);
                }
                // Now lower them all
                for (id, n, term) in v {
                    let (pre_id, _state) = cxt.db.lookup_intern_def(*id);

                    let val = term.lower(cxt);

                    let val2 = cxt.get_or_reserve(pre_id);
                    cxt.builder.redirect(val2, val);
                    prod.push((*n, val));

                    lower_children(*id, cxt);
                }
                prod.sort_by_key(|(n, _)| n.get(cxt.db));
                let prod: SmallVec<_> = prod.into_iter().map(|(_, x)| x).collect();

                cxt.builder.product(t, prod)
            }
            Term::Struct(StructKind::Sig, v) => {
                let mut v: Vec<_> = v.iter().map(|(_, n, x)| (*n, x.lower(cxt))).collect();
                v.sort_by_key(|(n, _)| n.get(cxt.db));
                let v: SmallVec<_> = v.into_iter().map(|(_, x)| x).collect();
                cxt.builder.prod_type(v)
            }
            // \x.f x
            // -->
            // fun a (x, r) = f x k
            // fun k y = r y
            Term::Clos(Lam, name, _icit, param_ty, body, effs_) => {
                let param_ty = (**param_ty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt);
                let mut params = vec![(
                    Some(cxt.db.lookup_intern_name(*name)),
                    param_ty.clone().lower(cxt),
                )];
                cxt.mcxt.eff_stack.push_scope(false, Span::empty());
                let mut effs = Vec::new();

                if !effs_.is_empty() {
                    // The function takes a continuation for each effect, plus a return continuation
                    for eff in effs_ {
                        let eff = eff.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt);
                        if matches!(eff, Val::App(Var::Builtin(Builtin::IO), _, _, _)) {
                            continue;
                        }
                        let name = eff.pretty(&cxt.mcxt).raw_string();
                        let cont_ty = cxt.builder.fun_type(2);
                        effs.push(eff);
                        params.push((Some(format!("$cont.{}", name)), cont_ty));
                    }
                }

                let args = cxt.builder.push_fun(params);
                cxt.local(*name, args[0], param_ty);
                for (k, e) in args.into_iter().skip(1).zip(effs) {
                    cxt.eff(e, k);
                }
                let ret = body.lower(cxt);

                let val = cxt.builder.pop_fun(ret);

                cxt.mcxt.eff_stack.pop_scope();
                cxt.pop_local();
                val
            }
            Term::Dot(x, m) => {
                let xty = x.ty(cxt.mcxt.size, &cxt.mcxt);
                let i = match xty.inline_top(&cxt.mcxt) {
                    Term::Struct(StructKind::Sig, mut v) => {
                        v.sort_by_key(|(_, n, _)| n.get(cxt.db));
                        v.into_iter()
                            .enumerate()
                            .find(|(_, (_, n, _))| n == m)
                            .map(|(i, _)| i)
                            .unwrap()
                    }
                    _ => unreachable!(),
                };
                let x = x.lower(cxt);
                cxt.builder.project(x, i)
            }
            Term::App(_icit, f, x) => {
                // Uncurry binops when possible
                if let Term::App(_, f2, y) = &**f {
                    if let Term::Var(Var::Builtin(Builtin::BinOp(op)), fty) = &**f2 {
                        let (_ity, signed) = fty.binop_ty(cxt);
                        let x = x.lower(cxt);
                        let y = y.lower(cxt);
                        return cxt.builder.binop(op.lower(), signed, y, x);
                    }
                }

                let fty = f.ty(cxt.mcxt.size, &cxt.mcxt);
                let fty = fty
                    .evaluate(&cxt.mcxt.env(), &cxt.mcxt)
                    .inline(cxt.mcxt.size, &cxt.mcxt);
                let f = f.lower(cxt);
                let x = x.lower(cxt);
                let (rty, effs) = match fty.unarc() {
                    Val::Clos(Pi, _, cl, effs) => (
                        {
                            let rty = (**cl).clone().vquote(cxt.mcxt.size, &cxt.mcxt);
                            cxt.local(cl.name, x, cl.ty.clone());
                            let rty = rty.lower(cxt);
                            cxt.pop_local();
                            rty
                        },
                        effs.clone(),
                    ),
                    Val::Fun(_, r, effs) => ((**r).clone().lower(cxt), effs.clone()),
                    _ => unreachable!(),
                };
                if effs.is_empty() {
                    cxt.builder.call(f, vec![x], rty)
                } else {
                    let mut args = vec![x];
                    let mut tcxt = cxt.mcxt.clone();
                    for eff in effs {
                        if matches!(eff, Val::App(Var::Builtin(Builtin::IO), _, _, _)) {
                            continue;
                        }
                        let i = cxt
                            .mcxt
                            .eff_stack
                            .find_eff(&eff, &mut tcxt)
                            .unwrap_or_else(|| {
                                panic!(
                                    "Could not find effect {:?} in context {:?}",
                                    eff, cxt.mcxt.eff_stack
                                )
                            });
                        args.push(cxt.eff_conts[i]);
                    }

                    cxt.builder.call(f, args, rty)
                }
            }
            Term::Fun(_, _, effs) | Term::Clos(Pi, _, _, _, _, effs) => {
                let mut nargs = 2;

                for eff in effs {
                    if matches!(eff, Term::Var(Var::Builtin(Builtin::IO), _)) {
                        continue;
                    }
                    nargs += 1;
                }
                cxt.builder.fun_type(nargs)
            }
            Term::Case(x, xty, cases, effs, ty) => lower_case(
                x,
                xty,
                cases,
                effs,
                (**ty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt),
                cxt,
            ),
        }
    }
}

fn lower_case(
    x: &Term,
    xty: &Term,
    cases: &[(Pat, Term)],
    effs: &[Term],
    ty: Val,
    cxt: &mut LCxt,
) -> ir::Val {
    let xty = xty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt);

    if effs.is_empty() {
        let x = x.lower(cxt);

        let before_level = cxt.mcxt.size;
        let cont = cases
            .iter()
            .rfold(PatCont::Unreachable, |rest, (pat, term)| PatCont::Pat {
                x,
                pat,
                cont: Box::new(PatCont::Term(term)),
                rest_size: before_level,
                rest: Box::new(rest),
            });
        let ret = cont.lower(ty, cxt);
        cxt.trunc_locals(before_level);
        ret
    } else {
        let env = cxt.mcxt.env();
        cxt.mcxt.eff_stack.push_scope(false, Span::empty());
        for e in effs {
            let e = e.clone().evaluate(&env, &cxt.mcxt);
            cxt.mcxt.eff_stack.push_eff(e);
        }
        let mut branches_pure: Vec<(&Pat, &Term)> = Vec::new();
        let mut branches_eff: Vec<Vec<(&Pat, &Pat, &Term)>> =
            (0..effs.len()).map(|_| Vec::new()).collect();
        let mut tcxt = cxt.mcxt.clone();
        for (pat, body) in cases {
            match pat {
                Pat::EffRet(pat) => {
                    branches_pure.push((pat, body));
                }
                Pat::Eff(eff, p, k) => {
                    let veff = (**eff).clone().evaluate(&env, &cxt.mcxt);
                    let i = cxt
                        .mcxt
                        .eff_stack
                        .find_eff(&veff, &mut tcxt)
                        .unwrap_or_else(|| panic!("Couldn't find effect {:?}", eff));
                    branches_eff[i].push((p, k, body));
                }
                pat => unreachable!("{:?}", pat),
            }
        }
        let effs = cxt.mcxt.eff_stack.pop_scope();

        let ret_ty = ty.clone().lower(cxt);

        cxt.catch(
            &effs,
            xty,
            ret_ty,
            x,
            |cxt, i, x, k| {
                // Required for the eff pattern
                let nothing = cxt.builder.reserve(None);
                cxt.local(cxt.db.intern_name(String::new()), nothing, Val::Type);
                let before_level = cxt.mcxt.size;

                let cont =
                    branches_eff[i]
                        .iter()
                        .rfold(PatCont::Unreachable, |rest, (px, pk, term)| PatCont::Pat {
                            x,
                            pat: px,
                            cont: Box::new(PatCont::Pat {
                                x: k,
                                pat: pk,
                                cont: Box::new(PatCont::Term(term)),
                                rest_size: before_level,
                                rest: Box::new(rest.clone()),
                            }),
                            rest_size: before_level,
                            rest: Box::new(rest),
                        });
                let ret = cont.lower(ty.clone(), cxt);
                cxt.trunc_locals(before_level);
                cxt.pop_local();
                ret
            },
            |cxt, x| {
                let before_level = cxt.mcxt.size;
                let cont = branches_pure
                    .iter()
                    .rfold(PatCont::Unreachable, |rest, (pat, term)| PatCont::Pat {
                        x,
                        pat,
                        cont: Box::new(PatCont::Term(term)),
                        rest_size: before_level,
                        rest: Box::new(rest),
                    });
                let ret = cont.lower(ty.clone(), cxt);
                cxt.trunc_locals(before_level);
                ret
            },
        )
    }
}

#[derive(Clone, Debug)]
enum PatCont<'a> {
    Unreachable,
    Term(&'a Term),
    Var(ir::Val, Name, &'a Term, Box<PatCont<'a>>),
    Pat {
        x: ir::Val,
        pat: &'a Pat,
        /// What to do next if the pattern matches
        cont: Box<PatCont<'a>>,
        /// The size that the context should be at for lowering `rest`
        rest_size: Size,
        /// What to do next if the pattern doesn't match
        rest: Box<PatCont<'a>>,
    },
}
impl<'a> PatCont<'a> {
    fn lower(&'a self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
        match self {
            PatCont::Unreachable => {
                let ty = ty.lower(cxt);
                cxt.builder.unreachable(ty)
            }
            PatCont::Term(x) => x.lower(cxt),
            PatCont::Var(x, name, vty, cont) => {
                cxt.local(
                    *name,
                    *x,
                    (**vty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt),
                );
                cont.lower(ty, cxt)
            }
            PatCont::Pat {
                x,
                pat,
                cont,
                rest_size,
                rest,
            } => pat.lower(*x, &cont, *rest_size, &rest, ty, cxt),
        }
    }
}

impl Literal {
    fn lower(self, w: ir::Width, cxt: &mut LCxt) -> ir::Val {
        match self {
            Literal::Positive(i) => cxt.builder.cons(ir::Constant::Int(w, i as i64)),
            Literal::Negative(i) => cxt.builder.cons(ir::Constant::Int(w, i)),
            Literal::Float(i) => cxt.builder.cons(ir::Constant::Float(match w {
                ir::Width::W32 => Float::F32((f64::from_bits(i) as f32).to_bits()),
                ir::Width::W64 => Float::F64(i),
                _ => unreachable!(),
            })),
            Literal::String(n) => cxt.builder.cons(ir::Constant::String(n.get(cxt.db))),
        }
    }
}

impl Pat {
    fn lower<'a>(
        &'a self,
        x: ir::Val,
        cont: &'a PatCont<'a>,
        rest_size: Size,
        rest: &'a PatCont<'a>,
        ty: VTy,
        cxt: &mut LCxt,
    ) -> ir::Val {
        match self {
            Pat::Any => cont.lower(ty, cxt),
            Pat::Var(n, vty) => {
                cxt.local(*n, x, (**vty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt));
                cont.lower(ty, cxt)
            }
            Pat::Lit(l, w, signed) => {
                let l = l.lower(*w, cxt);
                let eq = cxt.builder.binop(ir::BinOp::Eq, *signed, l, x);
                let lty = ty.clone().lower(cxt);
                cxt.if_expr(eq);

                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                cxt.trunc_locals(rest_size);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
            }
            Pat::Bool(b) => {
                let l = cxt
                    .builder
                    .cons(ir::Constant::Int(ir::Width::W1, *b as i64));
                let eq = cxt.builder.binop(ir::BinOp::Eq, false, l, x);
                let lty = ty.clone().lower(cxt);
                cxt.if_expr(eq);

                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                cxt.trunc_locals(rest_size);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
            }
            Pat::Cons(id, xty, args) => {
                // TODO unarc_owned() or something
                let (tid, sid, targs) =
                    match xty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt).unarc() {
                        Val::App(Var::Type(tid, sid), _, sp, _) => (
                            *tid,
                            *sid,
                            sp.iter().map(|e| e.assert_app().1.clone()).collect(),
                        ),
                        Val::App(Var::Rec(id), _, sp, _) => cxt
                            .scope_ids
                            .get(id)
                            .map(|&(x, y)| {
                                (x, y, sp.iter().map(|e| e.assert_app().1.clone()).collect())
                            })
                            .expect("Datatypes should be lowered before their constructors"),
                        x => unreachable!("{:?}", x),
                    };
                let lret_ty = ty.clone().lower(cxt);

                let idx = cxt
                    .db
                    .lookup_intern_scope(sid)
                    .iter()
                    .filter_map(|&(_name, id)| {
                        let info = cxt.db.elaborate_def(id).ok()?;
                        match &**info.term.as_ref().unwrap() {
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
                    .rfold(cont.clone(), |cont, (i, (v, pat))| {
                        let x = cxt.builder.project(product, i);
                        let cont = PatCont::Pat {
                            x,
                            pat,
                            cont: Box::new(cont),
                            rest_size,
                            rest: Box::new(rest.clone()),
                        };
                        // Add the shadow variable first
                        match v {
                            Some((name, ty)) => PatCont::Var(x, *name, ty, Box::new(cont)),
                            None => cont,
                        }
                    });
                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                cxt.trunc_locals(rest_size);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lret_ty)
            }
            Pat::Or(a, b) => {
                let rest = PatCont::Pat {
                    x,
                    pat: b,
                    cont: Box::new(cont.clone()),
                    rest_size,
                    rest: Box::new(rest.clone()),
                };
                a.lower(x, cont, cxt.mcxt.size, &rest, ty, cxt)
            }
            Pat::Eff(_, _, _) | Pat::EffRet(_) => {
                unreachable!("should have gotten rid of eff patterns earlier")
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
        db.set_input_files(vec![id]);
        let mut mcxt = ModCxt::new(&db);
        for &def in &*db.top_level(id) {
            if let Ok(info) = db.elaborate_def(def) {
                mcxt.local(def, |lcxt| info.term.as_ref().unwrap().lower(lcxt));
            }
        }
        println!("module: {}", mcxt.module.emit());
    }
}
