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
            module: ir::Module::new(),
        }
    }

    pub fn local(&mut self, def: DefId, f: impl FnOnce(&mut LCxt) -> ir::Val) {
        let (pre, state) = self.db.lookup_intern_def(def);
        let locals = IVec::new();
        let mut lcxt = LCxt::new(
            self.db,
            MCxt::from_state(state, MCxtType::Local(def)),
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
/// ```durin
/// val Console_eff = ({} | { I32 });
/// # The thing passed to this is created by a `catch-of` construct
/// val ContTy_Console_inner = fun (Console_eff, fun(Any));
///
/// # We generally store a `**continuation`
/// # When a new `**continuation` is passed, we do `*old = Redirect(*new);`
/// # Then, when calling the continuation, we collapse them so it's amortized O(1) instead of O(number of catches).
/// val ContTy_Console = ref (ContTy_Console_inner | ContTy_Console);
///
/// # This is the logic to collapse the `**continuation` and then call the newest one
/// fun runcont_Console (x : Console_eff, ret : fun(Any), k : ref ContTy_Console) = refget k r2;
/// fun r2 (k2 : ref (ContTy_Console_inner | ContTy_Console)) = refget k2 r3;
/// fun r3 (k3 : (ContTy_Console_inner | ContTy_Console)) = ifcase 0 k3 rF r4;
/// fun r4 () = ifcase 1 k3 r5 unreachable;
/// fun r5 (k4 : ContTy_Console) = refset k k4 r6;
/// fun r6 () = runcont_Console x ret k;
/// fun rF (kF : fun (Console_eff, fun(Any))) = kF x ret;
///
/// # A function that uses effects
/// fun Console_Print (i : I32, k_eff : ref ContTy_Console, k_ret : fun({})) = runcont_Console (Console_eff:1 { i }) k_ret k_eff;
///
/// # An example of an effect continuation, with type `ContTy_Console_inner`
/// # Here the pattern matching on the effect is in `fun catch_rest (eff : Console_eff, k : fun(Any, ref ContTy_Console, fun(Any)))`
/// fun cont_Console (x : Console_eff, k : fun(Any)) = catch_rest (x, cont_wrapper);
///
/// # We need to wrap the continuation in a function that sets the old `**continuation` appropriately
/// # `last_k_eff` and `last_k_ret` are the effect and return continuations generated for this `catch`
/// fun cont_wrapper (val : Any, k_eff : ref ContTy_Console, k_ret : fun(Any)) = refget last_k_eff c2;
/// # It's possible they didn't collapse it last time, so do it now
/// fun c2 (k2 : ref (ContTy_Console_inner | ContTy_Console)) = refget k2 c3;
/// fun c3 (k3 : (ContTy_Console_inner | ContTy_Console)) = ifcase 1 k3 c4 cF;
/// # If we get to c4, it's been redirected and not collapsed, so do that now
/// fun c4 (k4 : ContTy_Console) = refset k k4 c5;
//// # Loop back and do it again
/// fun c5 () = refget k_eff c2;
/// # We're done collapsing, so we can set it to the new continuation
/// fun cF () = refget k_eff cF2;
/// fun cF2 (k_eff2 : ContTy_Console) = refset k2 (_:1 k_eff2) cF3;
/// # Do the same thing for the return continuation, then call cL
/// fun cF3 = ...
/// # Last, call the original one-argument continuation we were passed
/// fun cL = k val;
/// ```
impl<'db> LCxt<'db> {
    /// The logic shared by `runcont_Console` and `cont_wrapper` above, which collapses the `**continuation` and returns its value of type `ContTy_Console_inner`
    fn collapse_continuation(&mut self, k: ir::Val) -> ir::Val {
        let any_ty = self.builder.cons(ir::Constant::TypeType);

        // val ContTy_Console_inner = fun (Console_eff, fun(Any));
        let kty_inner = self.builder.fun_type(2);

        // val ContTy_Console = ref (ContTy_Console_inner | ContTy_Console);
        let kty = {
            let kty = self.builder.reserve(None);
            let sum_ty = self.builder.sum_type(&[kty_inner, kty] as &_);
            let vty = self.builder.ref_type(sum_ty);
            self.builder.redirect(kty, vty);
            kty
        };

        // fun r0 () = refget k r2;
        let (r0, _) = self.builder.push_frame(vec![]);
        let k2 = self.builder.refget(k);

        // fun r2 (k2 : ref (ContTy_Console_inner | ContTy_Console)) = refget k2 r3;
        let k3 = self.builder.refget(k2);

        // fun r3 (k3 : (ContTy_Console_inner | ContTy_Console)) = ifcase 0 k3 rF r4;
        let k_f = self.builder.ifcase(0, k3, kty_inner);
        self.builder.otherwise(&[k_f] as &_);

        // fun r4 () = ifcase 1 k3 r5 unreachable;
        let k4 = self.builder.ifcase(1, k3, kty);

        // fun r5 (k4 : ContTy_Console) = refset k k4 r6;
        self.builder.refset(k, k4);

        // fun r6 () = r0;
        self.builder.call_raw(r0, &[] as &_);

        // The `unreachable` instruction in the above ifcase
        self.builder.otherwise(&[] as &_);
        self.builder.unreachable(any_ty);
        self.builder.endif(&[] as &_);

        // fun rF (kF : fun (Console_eff, fun(Any))) = <the rest of the program>;
        self.builder.endif(&[(k_f, kty_inner)] as &_)[0]
    }

    fn raise_effect(&mut self, k: ir::Val, eff_val: ir::Val, ret_ty: ir::Val) -> ir::Val {
        let k = self.collapse_continuation(k);
        self.builder.call(k, &[eff_val] as &_, ret_ty)
    }

    fn eff_cont_ty(&mut self, name: impl Into<String>) -> ir::Val {
        // val ContTy_Console_inner = fun (Console_eff, fun(Any));
        let kty_inner = self.builder.fun_type(2);

        // val ContTy_Console = ref (ContTy_Console_inner | ContTy_Console);
        let kty = self.builder.reserve(Some(name.into()));
        let sum_ty = self.builder.sum_type(&[kty_inner, kty] as &_);
        let vty = self.builder.ref_type(sum_ty);
        self.builder.redirect(kty, vty);

        // ref ContTy_Console
        self.builder.ref_type(kty)
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
        let any_ty = self.builder.cons(ir::Constant::TypeType);

        // We need to wrap the continuation in a function that sets the old `**continuation` appropriately
        // `old_conts` are the continuations we're making to pass to `term`, but the code here is part of the continuation wrapper,
        // which runs after `term` has raised an effect and we have new continuations, so from that perspective they're old
        let mut old_conts = Vec::new();
        // let mut old_cont_inners = Vec::new();
        let mut ktys = Vec::new();
        let mut etys = Vec::new();
        let mut offset_start = 100000;
        for (i, eff) in effs.iter().enumerate() {
            if matches!(eff, Val::App(Var::Builtin(Builtin::IO), _, _, _)) {
                offset_start = i;
                continue;
            }
            let leff = eff
                .clone()
                .lower(Val::builtin(Builtin::Eff, Val::Type), self);

            // val ContTy_Console_inner = fun (Console_eff, fun(Any));
            let kty_inner = self.builder.fun_type(2);

            // val ContTy_Console = ref (ContTy_Console_inner | ContTy_Console);
            let kty = self.builder.reserve(None);
            let sum_ty = self.builder.sum_type(&[kty_inner, kty] as &_);
            let vty = self.builder.ref_type(sum_ty);
            self.builder.redirect(kty, vty);

            let cont = self.builder.refnew(kty);
            let kty = self.builder.ref_type(kty);

            old_conts.push(cont);
            etys.push(leff);
            ktys.push(kty);
        }

        // Define the pure continuation
        let pure_cont_ty = self.builder.fun_type(1);
        let pure_cont_inner = self.builder.reserve(None);
        let pure_cont = self.builder.refnew(pure_cont_ty);
        self.builder.refset(pure_cont, pure_cont_inner);

        // Start defining `cont_wrapper` by updating the effect continuations
        let args: Vec<_> = std::iter::once((None, any_ty))
            .chain(ktys.iter().copied().map(|x| (None, x)))
            .chain(std::iter::once((None, pure_cont_ty)))
            .collect();
        let new_conts = self.builder.push_fun_raw(&*args);
        for (&old, &new) in old_conts.iter().zip(new_conts.iter().skip(1)) {
            // Make sure it's collapsed so we're updating the newest **continuation
            self.collapse_continuation(old);
            // Now update it: `**old = Redirect(new)`
            let old = self.builder.refget(old);
            let sum_ty = {
                // val ContTy_Console_inner = fun (Console_eff, fun(Any));
                let kty_inner = self.builder.fun_type(2);

                // val ContTy_Console = ref (ContTy_Console_inner | ContTy_Console);
                let kty = self.builder.reserve(None);
                let sum_ty = self.builder.sum_type(&[kty_inner, kty] as &_);
                let vty = self.builder.ref_type(sum_ty);
                self.builder.redirect(kty, vty);

                sum_ty
            };
            let new = self.builder.refget(new);
            let sum = self.builder.inject_sum(sum_ty, 1, new);
            self.builder.refset(old, sum);
        }

        // We also need to update the pure continuation, but no collapsing is necessary
        self.builder.refset(pure_cont, *new_conts.last().unwrap());

        // The raw one-argument continuation, passed to `cont_wrapper_wrapper`
        let cont_inner = self.builder.reserve(Some("cont_inner".into()));
        let cont_wrapper = self.builder.pop_fun_raw(cont_inner, &new_conts[0..1]);
        let cont_wrapper_ty = self.builder.type_of(cont_wrapper);
        let cont_wrapper_wrapper = {
            let afun_ty = self.builder.fun_type(1);
            let inner = self.builder.push_fun(&[(None, afun_ty)] as &_);
            self.builder.redirect(cont_inner, inner[0]);
            self.builder.pop_fun(cont_wrapper)
        };

        // Define the return continuation
        // This is where we'll pass the result of `eff()` or `pure()`
        // Right now it's empty, but we'll redirect it to a `push_frame()` call at the end
        // It has type `fun(ret_ty)`
        // This is different than `self.rcont`, which will point to `pure()`
        let ret_cont = self.builder.reserve(None);

        // Now define the actual effect continuations, which inject to `eff_sum_ty` and pass it to `eff_cont`
        for (i, (&old_ptr, eff)) in old_conts.iter().zip(etys).enumerate() {
            let i = if i >= offset_start { i + 1 } else { i };

            let afun_ty = self.builder.fun_type(1);
            let args = self
                .builder
                .push_fun_raw(&[(None, eff), (None, afun_ty)] as &_);

            let cont_wrapper = self
                .builder
                .call(cont_wrapper_wrapper, &args[1..], cont_wrapper_ty);

            let ret = do_eff(self, i, args[0], cont_wrapper);
            let fun = self.builder.pop_fun_raw(ret_cont, &[ret] as &_);

            // val ContTy_Console_inner = fun (Console_eff, fun(Any));
            let kty_inner = self.builder.fun_type(2);

            // val ContTy_Console = ref (ContTy_Console_inner | ContTy_Console);
            let kty = self.builder.reserve(None);
            let sum_ty = self.builder.sum_type(&[kty_inner, kty] as &_);
            let vty = self.builder.ref_type(sum_ty);
            self.builder.redirect(kty, vty);

            let cont = self.builder.inject_sum(sum_ty, 0, fun);
            let cont_ptr = self.builder.refnew(sum_ty);
            self.builder.refset(cont_ptr, cont);
            self.builder.refset(old_ptr, cont_ptr);
        }

        // Now we need to define the pure continuation, to be run if no effects occur
        // It has type `fun(pure_ty)`
        {
            let args = self.builder.push_fun_raw(&[(None, ret_ty)] as &_);
            let ret = do_pure(self, args[0]);
            let fun = self.builder.pop_fun_raw(ret_cont, &[ret] as &_);
            self.builder.redirect(pure_cont_inner, fun);
        };

        // All the continuations are defined, now set the required state and lower `term`
        self.mcxt.eff_stack.push_scope(false, Span::empty());
        for (old, eff) in old_conts.into_iter().zip(effs) {
            let i = self.mcxt.eff_stack.len();
            if i >= self.eff_conts.len() {
                self.eff_conts.push(old);
            } else {
                self.eff_conts[i] = old;
            }
            self.mcxt.eff_stack.push_eff(eff.clone());
        }
        let old_rcont = self.rcont;
        self.rcont = Some(pure_cont);

        // Lower `term` with type `pure_ty`
        let ret = term.lower(pure_ty, self);
        // Then call `*rcont` with the result
        let rcont = self.builder.refget(pure_cont);
        self.builder.call_raw(rcont, &[ret] as &_);

        // Reset the state and return the value passed to `ret_cont`
        self.mcxt.eff_stack.pop_scope();
        self.rcont = old_rcont;

        let (frame, args) = self.builder.push_frame(vec![(ret, ret_ty)]);
        self.builder.redirect(ret_cont, frame);
        args[0]
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
                cl.vquote(at, &cxt.mcxt, cxt.db).cons_parent(at.inc(), cxt)
            }
            Val::Clos(Pi, _, cl, mut effs) => {
                assert_eq!(effs.len(), 1);
                let (tid, sid, _) = effs.pop().unwrap().cons_parent(at, cxt);
                let to = cl.vquote(at, &cxt.mcxt, cxt.db);
                (tid, sid, Some(to))
            }
            Val::Arc(x) => IntoOwned::<Val>::into_owned(x).cons_parent(at, cxt),
            x => unreachable!("{:?}", x),
        }
    }

    pub fn lower(self, ty: VTy, cxt: &mut LCxt) -> ir::Val {
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
                        .quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                        .lower(ty, cxt);
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
            let (pre_id, _state) = cxt.db.lookup_intern_def(def);
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
                                Val::Clos(Pi, i, cl, _) => {
                                    let from = cl.ty.clone();
                                    ty_args.push(Elim::App(
                                        i,
                                        Val::local(cxt.mcxt.size.next_lvl(), from.clone()),
                                    ));
                                    cxt.mcxt.define(cl.name, NameInfo::Local(from), cxt.db);
                                    tty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt, cxt.db);
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
                            .quote(cxt.mcxt.size, &cxt.mcxt, cxt.db)
                            .evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db);
                        loop {
                            match cty {
                                Val::Clos(Pi, _, cl, mut effs) => {
                                    let from = cl.ty.clone();
                                    cxt.mcxt
                                        .define(cl.name, NameInfo::Local(from.clone()), cxt.db);
                                    if effs.is_empty() {
                                        cty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt, cxt.db);
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
                            cxt.db,
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
                                let v = v
                                    .clone()
                                    .quote(env.size, &tcxt, cxt.db)
                                    .evaluate(&env, &tcxt, cxt.db);
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
                    let mut sigma = cxt.builder.sigma();
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
                                    .quote(env.size, &cxt.mcxt, cxt.db)
                                    .evaluate(&env, &cxt.mcxt, cxt.db);

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
                                    // cxt.builder.cons(ir::Constant::Unreachable)
                                    sigma.add(from.clone().lower(Val::Type, cxt), &mut cxt.builder)
                                } else {
                                    // It doesn't have a solution, so it remains in the product type
                                    keep.push(true);
                                    env.push(None);
                                    sigma.add(from.clone().lower(Val::Type, cxt), &mut cxt.builder)
                                };

                                // Define the variable and go to the next level
                                cxt.local(cl.name, val, from);
                                cty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt, cxt.db);
                                i += 1;
                                if !effs.is_empty() {
                                    break;
                                }
                            }
                            Val::Fun(from, to, effs) => {
                                // Quote-evaluate to apply substitutions from the environment
                                let from = from
                                    .quote(env.size, &cxt.mcxt, cxt.db)
                                    .evaluate(&env, &cxt.mcxt, cxt.db);

                                // We know we're keeping this one, since we can't solve a non-pi parameter
                                keep.push(true);

                                // Don't add the parameter to the context, since it's not a pi
                                sigma.add(from.clone().lower(Val::Type, cxt), &mut cxt.builder);
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
    fn lower(self, ty: &VTy, cxt: &mut LCxt) -> ir::Val {
        match self {
            Builtin::I32 => cxt.builder.cons(ir::Constant::IntType(ir::Width::W32)),
            Builtin::I64 => cxt.builder.cons(ir::Constant::IntType(ir::Width::W64)),
            // Bool translates to i1
            Builtin::Bool => cxt.builder.cons(ir::Constant::IntType(ir::Width::W1)),
            Builtin::BinOp(op) => {
                let ity = match ty {
                    Val::Fun(ity, _, _) => (**ity).clone().lower(Val::Type, cxt),
                    _ => unreachable!(),
                };
                let a = cxt.builder.push_fun([(None, ity)]);
                let b = cxt.builder.push_fun([(None, ity)]);
                let val = cxt.builder.binop(op.lower(), a[0], b[0]);
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
        }
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
                Var::Builtin(b) => b.lower(&ty, cxt),
                Var::Local(i) => *cxt.locals.get(*i),
                Var::Top(i) => {
                    let (i, _) = cxt.db.lookup_intern_def(*i);
                    cxt.get_or_reserve(i)
                }
                Var::Rec(i) => cxt.get_or_reserve(*i),
                Var::Meta(_) => panic!("unsolved meta passed to lower()"),
                Var::Type(tid, sid) => {
                    let (pre, _) = cxt.db.lookup_intern_def(*tid);
                    cxt.scope_ids.insert(pre, (*tid, *sid));

                    let mut ty = ty;
                    let mut funs = Vec::new();
                    let mut targs = Vec::new();
                    loop {
                        match ty {
                            Val::Clos(Pi, _, cl, _) => {
                                let from = cl.ty.clone();
                                targs.push(Val::local(cxt.mcxt.size.next_lvl(), from.clone()));

                                let lty = from.clone().lower(Val::Type, cxt);
                                let p = cxt.builder.push_fun([(None, lty)]);
                                cxt.local(cl.name, p[0], from);
                                funs.push((lty, true));
                                // Make sure to vquote outside of the closure
                                ty = cl.vquote(cxt.mcxt.size.dec(), &cxt.mcxt, cxt.db);
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
                    let (tid, sid, base_ty) = ty.clone().cons_parent(cxt.mcxt.size, cxt);

                    // TODO should this Durin-function-from-Pika-type be its own function?
                    let mut ty = ty;
                    let mut funs = Vec::new();
                    let eff_cont = loop {
                        match ty {
                            Val::Clos(Pi, _, cl, mut effs) => {
                                let from = cl.ty.clone();
                                let lty = from.clone().lower(Val::Type, cxt);

                                let name = cl.name;
                                let to = cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db);

                                if effs.is_empty() {
                                    ty = to;
                                    let p = cxt.builder.push_fun([(None, lty)]);
                                    cxt.local(name, p[0], from);
                                    funs.push((p[0], ty.clone().lower(Val::Type, cxt), true));
                                } else {
                                    assert_eq!(effs.len(), 1);
                                    let eff = effs.pop().unwrap();

                                    let ename = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                                    let cont_ty = cxt.eff_cont_ty(&ename);

                                    ty = eff;
                                    // The function takes a continuation for each effect, plus two return continuations
                                    // The first one is for returning to the outermost `catch` and isn't manually called, just passed around
                                    // (except in the implementation of `catch`)
                                    // The second one is the normal return continuation, which this function will call when it's done
                                    let p = cxt.builder.push_fun([
                                        (None, lty),
                                        (Some(format!("$cont.{}", ename)), cont_ty),
                                    ]);
                                    cxt.local(name, p[0], from);
                                    funs.push((p[0], ty.clone().lower(Val::Type, cxt), false));
                                    break Some(p[1]);
                                }
                            }
                            Val::Fun(from, to, mut effs) => {
                                let from = from.lower(Val::Type, cxt);

                                if effs.is_empty() {
                                    ty = *to;
                                    let p = cxt.builder.push_fun([(None, from)]);
                                    funs.push((p[0], ty.clone().lower(Val::Type, cxt), false));
                                } else {
                                    assert_eq!(effs.len(), 1);
                                    let eff = effs.pop().unwrap();

                                    let name = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                                    let cont_ty = cxt.eff_cont_ty(&name);

                                    ty = eff;
                                    // The function takes a continuation for each effect, plus two return continuations
                                    // The first one is for returning to the outermost `catch` and isn't manually called, just passed around
                                    // (except in the implementation of `catch`)
                                    // The second one is the normal return continuation, which this function will call when it's done
                                    let p = cxt.builder.push_fun([
                                        (None, from),
                                        (Some(format!("$cont.{}", name)), cont_ty),
                                    ]);
                                    funs.push((p[0], ty.clone().lower(Val::Type, cxt), false));
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
                        let eff_cont = eff_cont.unwrap();
                        let base_ty = base_ty.lower(Val::Type, cxt);

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

                    let ty = cxt.db.def_type(*id).unwrap();

                    let val = term.lower((*ty).clone(), cxt);

                    let val2 = cxt.get_or_reserve(pre_id);
                    cxt.builder.redirect(val2, val);

                    lower_children(*id, cxt);
                }
                // And return the last one
                if let Some((id, term)) = sc.last() {
                    let (pre_id, _state) = cxt.db.lookup_intern_def(*id);

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
            Term::Clos(Lam, name, _icit, _arg_ty, body, _effs) => {
                let (param_ty, ret_ty, effs_) = match ty.inline(cxt.mcxt.size, cxt.db, &cxt.mcxt) {
                    Val::Fun(from, to, effs) => {
                        // inc() because we're evaluate()-ing it inside the lambda
                        (*from, *to, effs)
                    }
                    Val::Clos(Pi, _, cl, effs) => (
                        cl.ty.clone(),
                        cl.vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db),
                        effs,
                    ),
                    _ => unreachable!(),
                };
                assert_eq!(cxt.mcxt.size, cxt.locals.size());
                let mut params = vec![(
                    Some(cxt.db.lookup_intern_name(*name)),
                    param_ty.clone().lower(Val::Type, cxt),
                )];
                cxt.mcxt.eff_stack.push_scope(false, Span::empty());
                let mut effs = Vec::new();

                if !effs_.is_empty() {
                    // The function takes a continuation for each effect, plus two return continuations
                    // The first one is for returning to the outermost `catch` and isn't manually called, just passed around
                    // (except in the implementation of `catch`)
                    // The second one is the normal return continuation, which this function will call when it's done
                    for eff in effs_ {
                        if matches!(eff, Val::App(Var::Builtin(Builtin::IO), _, _, _)) {
                            continue;
                        }
                        let name = eff.pretty(cxt.db, &cxt.mcxt).raw_string();
                        let cont_ty = cxt.eff_cont_ty(&name);
                        effs.push(eff);
                        params.push((Some(format!("$cont.{}", name)), cont_ty))
                    }
                }

                let args = cxt.builder.push_fun(params);
                cxt.local(*name, args[0], param_ty);
                for (k, e) in args.into_iter().skip(1).zip(effs) {
                    cxt.eff(e, k);
                }
                let ret = body.lower(ret_ty, cxt);

                let val = cxt.builder.pop_fun(ret);

                cxt.mcxt.eff_stack.pop_scope();
                cxt.pop_local();
                val
            }
            Term::App(_icit, f, x) => {
                // Uncurry binops when possible
                if let Term::App(_, f2, y) = &**f {
                    if let Term::Var(Var::Builtin(Builtin::BinOp(op)), fty) = &**f2 {
                        let ity = match &**fty {
                            Term::Fun(ity, _, _) => {
                                (**ity).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db)
                            }
                            _ => unreachable!(),
                        };
                        let x = x.lower(ity.clone(), cxt);
                        let y = y.lower(ity, cxt);
                        return cxt.builder.binop(op.lower(), y, x);
                    }
                }

                let ret_ty = ty;
                let ret_ty = ret_ty.lower(Val::Type, cxt);
                let fty = f.ty(cxt.mcxt.size, &cxt.mcxt, cxt.db);
                let fty = fty
                    .clone()
                    .evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db)
                    .inline(cxt.mcxt.size, cxt.db, &cxt.mcxt);
                let (xty, rty, effs) = match fty.unarc() {
                    Val::Clos(Pi, _, cl, effs) => (
                        cl.ty.clone(),
                        cl.clone().vquote(cxt.mcxt.size, &cxt.mcxt, cxt.db),
                        effs.clone(),
                    ),
                    Val::Fun(x, y, effs) => ((**x).clone(), (**y).unarc().clone(), effs.clone()),
                    _ => unreachable!(),
                };
                let f = f.lower(fty, cxt);
                let x = x.lower(xty, cxt);
                if effs.is_empty() {
                    cxt.builder.call(f, vec![x], ret_ty)
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
                            .find_eff(&eff, cxt.db, &mut tcxt)
                            .unwrap_or_else(|| {
                                panic!(
                                    "Could not find effect {:?} in context {:?}",
                                    eff, cxt.mcxt.eff_stack
                                )
                            });
                        args.push(cxt.eff_conts[i]);
                    }

                    // If the call raised an effect, the location of the catch to return to changed
                    // So store the updated effect and return continuations in the context
                    let rty = rty.lower(Val::Type, cxt);
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
            Term::Error => panic!("type errors should have been caught by now!"),
            Term::Case(x, xty, cases, effs, _) => lower_case(x, xty, cases, effs, ty, cxt),
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
    let xty = xty.clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db);

    if effs.is_empty() {
        let x = x.lower(xty, cxt);

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
            let e = e.clone().evaluate(&env, &cxt.mcxt, cxt.db);
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
                    let veff = (**eff).clone().evaluate(&env, &cxt.mcxt, cxt.db);
                    let i = cxt
                        .mcxt
                        .eff_stack
                        .find_eff(&veff, cxt.db, &mut tcxt)
                        .unwrap_or_else(|| panic!("Couldn't find effect {:?}", eff));
                    branches_eff[i].push((p, k, body));
                }
                pat => unreachable!("{:?}", pat),
            }
        }
        let effs = cxt.mcxt.eff_stack.pop_scope();

        let ret_ty = ty.clone().lower(Val::Type, cxt);

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
                let ty = ty.lower(Val::Type, cxt);
                cxt.builder.unreachable(ty)
            }
            PatCont::Term(x) => x.lower(ty, cxt),
            PatCont::Var(x, name, vty, cont) => {
                cxt.local(
                    *name,
                    *x,
                    (**vty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db),
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
                cxt.local(
                    *n,
                    x,
                    (**vty).clone().evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db),
                );
                cont.lower(ty, cxt)
            }
            Pat::Lit(l, w) => {
                let l = l.lower(*w, cxt);
                let eq = cxt.builder.binop(ir::BinOp::IEq, l, x);
                cxt.if_expr(eq);

                let yes = cont.lower(ty.clone(), cxt);

                cxt.otherwise(yes);

                let lty = ty.clone().lower(Val::Type, cxt);
                cxt.trunc_locals(rest_size);
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
                cxt.trunc_locals(rest_size);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
            }
            Pat::Cons(id, xty, args) => {
                // TODO unarc_owned() or something
                let (tid, sid, targs) = match xty
                    .clone()
                    .evaluate(&cxt.mcxt.env(), &cxt.mcxt, cxt.db)
                    .unarc()
                {
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

                // if x.id() == 704 {
                //     eprintln!("{:?} -> {:?}: tid={:?}, sid={:?}, targs={:?}", cxt.mcxt.size, rest_size, tid, sid, targs);
                //     let (ltys, _) = lower_datatype(tid, sid, targs, cxt);
                //     let lty = ltys[idx];
                //     panic!("Got {:?}", lty);
                // }
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

                let lty = ty.clone().lower(Val::Type, cxt);
                cxt.trunc_locals(rest_size);
                let no = rest.lower(ty, cxt);

                cxt.endif(no, lty)
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
        let mut mcxt = ModCxt::new(&db);
        for &def in &*db.top_level(id) {
            if let Ok(info) = db.elaborate_def(def) {
                mcxt.local(def, |lcxt| info.term.lower((*info.typ).clone(), lcxt));
            }
        }
        println!("module: {}", mcxt.module.emit());
    }
}
