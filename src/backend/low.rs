use crate::common::*;
use lazy_static::lazy_static;
use std::{collections::HashSet, num::NonZeroU32, sync::RwLock};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd)]
pub struct Val(NonZeroU32);
impl Val {
    pub fn num(self) -> u32 {
        self.0.get() - 1
    }
}
lazy_static! {
    static ref VAL_NUM: RwLock<u32> = RwLock::new(0);
}
pub fn next_val() -> Val {
    let mut n = VAL_NUM.write().unwrap();
    *n += 1;
    Val(NonZeroU32::new(*n).unwrap())
}

// Example program:
//
// let imul = fun x: i32 => fun y: i32 => x * y in
// let square = fun x: i32 => imul x x in
// halt (square 5)
//
// Roughly corresponds to:
//
// let imul = fun x k =>
//    let cont = fun y k2 =>
//       let r = x * y
//       in k2 r
//    in k cont
// in let square = fun x k =>
//   let cont = fun r => r x k
//   in imul x cont
// in square 5 halt

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Unit,
    Int(u32),
    Fun,  //(/*Box<Ty>, */Box<Ty>),
    Cont, //(Box<Ty>),
    Struct(Vec<Ty>),
    /// Used for unknown types; represents a location on the stack, with a size
    Dyn(Val),
    /// Low IR unions are *not* tagged automatically, they should be in a struct with a tag.
    /// They're dynamically sized to whichever variant they actually are.
    /// That does mean we store the size redundantly, so in the future that may change.
    Union(Vec<Ty>),
    /// Represents a type with zero information known at compile time.
    /// It *must* be dynamically sized, i.e. be a pointer to a size
    Unknown,
}

/// A primitive expression, that actually returns a value
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    Unit,
    IntConst(u32, u64),
    IntOp(Val, IntOp, Val),
    CompOp(Val, CompOp, Val),
    Struct(Vec<(Val, Ty)>),
    Project(Ty, Val, u32),
    /// `Variant` creates a union type with given payload
    Variant(Ty, Val, u32),
    /// `AsVariant` extracts the payload from the given union type
    AsVariant(Ty, Val, u32),
    Val(Val),
    Cont {
        arg: Val,
        arg_ty: Ty,
        body: Box<Low>,
        upvalues: Vec<(Val, Ty)>,
    },
    Fun {
        arg: Val,
        arg_ty: Ty,
        cont: Val,
        body: Box<Low>,
        upvalues: Vec<(Val, Ty)>,
    },
}
impl From<i32> for Expr {
    fn from(i: i32) -> Expr {
        Expr::IntConst(32, i as u32 as u64)
    }
}
impl<T: Into<Expr> + Copy> From<&T> for Expr {
    fn from(i: &T) -> Expr {
        (*i).into()
    }
}

/// A CPS term, that doesn't return a value, it calls a continuation (unless it halts)
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Low {
    Let(Val, Expr, Box<Low>),
    /// Call(f, x: T, k)
    Call(Val, Ty, Val, Val),
    /// ContCall(k, x: T)
    ContCall(Val, Ty, Val),
    /// Global(name, k)
    Global(String, Val),
    IfElse(Val, Box<Low>, Box<Low>),
    Unreachable,
    Halt(Val),
}

#[derive(Clone)]
pub struct LCtx<'a> {
    to_val: HashMap<Sym, Val>,
    tys: HashMap<Val, Ty>,
    pub ectx: ECtx<'a>,
}
impl<'a> LCtx<'a> {
    pub fn next_val(&mut self, t: Ty) -> Val {
        let v = next_val();
        self.tys.insert(v, t);
        v
    }

    pub fn get(&self, x: Sym) -> Option<Val> {
        self.to_val.get(&x).copied()
    }

    pub fn set(&mut self, x: Sym, v: Val) {
        self.to_val.insert(x, v);
    }
}
impl<'a> From<ECtx<'a>> for LCtx<'a> {
    fn from(ectx: ECtx<'a>) -> Self {
        LCtx {
            to_val: HashMap::new(),
            tys: HashMap::new(),
            ectx,
        }
    }
}
impl<'a> Scoped for LCtx<'a> {
    fn scope(&self) -> ScopeId {
        self.ectx.scope()
    }
}
impl<'a> HasBindings for LCtx<'a> {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.database().bindings_ref()
    }
}
impl<'a> HasDatabase for LCtx<'a> {
    fn database(&self) -> &dyn MainGroup {
        self.ectx.database()
    }
}

impl Ty {
    /// Types can have free variables (that's dependent types!), so any term that needs to know the size of types needs to keep them around.
    pub fn fvs(&self, set: &mut HashSet<Val>) {
        match self {
            Ty::Dyn(v) => {
                set.insert(*v);
            }
            Ty::Struct(v) | Ty::Union(v) => {
                for i in v {
                    i.fvs(set)
                }
            }
            Ty::Int(_) | Ty::Fun | Ty::Cont | Ty::Unit | Ty::Unknown => {}
        }
    }
}

impl Expr {
    pub fn fvs(&self, set: &mut HashSet<Val>) {
        match self {
            Expr::IntConst(_, _) | Expr::Unit => (),
            Expr::IntOp(a, _, b) | Expr::CompOp(a, _, b) => {
                set.insert(*a);
                set.insert(*b);
            }
            Expr::Struct(v) => set.extend(v.iter().map(|(x, _)| *x)),
            Expr::Project(t, r, _) => {
                t.fvs(set);
                set.insert(*r);
            }
            Expr::Variant(t, v, _) | Expr::AsVariant(t, v, _) => {
                t.fvs(set);
                set.insert(*v);
            }
            Expr::Val(v) => {
                set.insert(*v);
            }
            // Closures essentially have this precomputed
            Expr::Cont { upvalues, .. } | Expr::Fun { upvalues, .. } => {
                for (i, t) in upvalues {
                    t.fvs(set);
                    set.insert(*i);
                }
            }
        }
    }
}

impl Low {
    pub fn fvs(&self) -> HashSet<Val> {
        match self {
            Low::Let(v, e, b) => {
                let mut set = b.fvs();
                e.fvs(&mut set);
                set.remove(v);
                set
            }
            Low::Call(a, _, b, c) => [*a, *b, *c].iter().copied().collect(),
            Low::ContCall(a, _, b) => [*a, *b].iter().copied().collect(),
            Low::Halt(v) | Low::Global(_, v) => {
                let mut set = HashSet::new();
                set.insert(*v);
                set
            }
            Low::IfElse(cond, yes, no) => {
                let mut a = yes.fvs();
                let b = no.fvs();
                a.extend(b);
                a.insert(*cond);
                a
            }
            Low::Unreachable => HashSet::new(),
        }
    }
}

fn order_upvalues(upvalues: &mut Vec<(Val, Ty)>, lctx: &LCtx) {
    // Start with a deterministic order
    upvalues.sort_by_key(|(x, _)| x.num());

    // Reorder upvalues and add extras so that upvalue types with dependencies on other upvalues are all resolved
    let mut i = 0;
    while i < upvalues.len() {
        let mut extra = HashSet::new();
        upvalues[i].1.fvs(&mut extra);
        // We build the upvalue dependencies in reverse order
        // So if the dependency we need is after us in `upvalues`, we're good
        extra.retain(|x| upvalues[i..].iter().all(|(k, _)| k != x));
        // We don't want duplicates, though
        upvalues.retain(|(x, _)| !extra.contains(x));

        upvalues.extend(
            extra
                .into_iter()
                .map(|x| (x, lctx.tys.get(&x).unwrap().clone())),
        );
        i += 1;
    }
    // And here we reverse it so dependencies are in the right order
    upvalues.reverse();
}

// Figures out the necessary upvalues, etc. to turn `rest` into a continuation you can pass around and call
pub fn make_cont(arg: Val, arg_ty: Ty, lctx: &LCtx, rest: Low) -> Expr {
    // We need to pass everything `rest` uses to the continuation
    let mut upvalues = rest.fvs();
    // The argument type might depend on something
    arg_ty.fvs(&mut upvalues);
    upvalues.remove(&arg);
    let mut upvalues: Vec<_> = upvalues
        .into_iter()
        .map(|x| (x, lctx.tys.get(&x).unwrap().clone()))
        .collect();

    order_upvalues(&mut upvalues, lctx);

    Expr::Cont {
        arg,
        arg_ty,
        body: Box::new(rest),
        upvalues,
    }
}

/// Get the width of the smallest IntType that can differentiate between all the things in `v`.
/// One of `i1, i8, i16, i32, i64`, or 0 if no tag is needed.
pub fn tag_width<T>(v: &[T]) -> u32 {
    let l = v.len();
    if l <= 1 {
        eprintln!("Warning: tag_width() when a tag isn't needed");
        1
    } else if l <= 2 {
        1
    } else if l <= 256 {
        8
    } else if l <= 1 << 16 {
        16
    } else if l <= 1 << 32 {
        32
    } else {
        64
    }
}

impl Elab {
    pub fn pass_args(&self, lctx: &mut LCtx, arg: Val, ty: &Ty, rest: Low) -> Low {
        match self {
            // These are types that don't bind anything
            Elab::Builtin(Builtin::Int)
            | Elab::Type(_)
            | Elab::Var(_, _, _)
            | Elab::Fun(_, _, _)
            | Elab::Data(_, _, _)
            | Elab::StructInline(_)
            | Elab::StructIntern(_)
            | Elab::App(_, _)
            | Elab::Unit => rest,
            Elab::Binder(s, t) => {
                let v = lctx.get(*s).unwrap();
                Low::Let(
                    v,
                    Expr::Val(arg),
                    Box::new(t.pass_args(lctx, arg, ty, rest)),
                )
            }
            Elab::Pair(x, y) => {
                let (xt, yt) = match ty {
                    Ty::Struct(v) if v.len() == 2 => (&v[0], &v[1]),
                    _ => panic!("expected pair type, found {:?}", ty),
                };
                let ax = lctx.next_val(xt.clone());
                let ay = lctx.next_val(yt.clone());
                let rest = Low::Let(
                    ay,
                    Expr::Project(ty.clone(), arg, 1),
                    Box::new(y.pass_args(lctx, ay, yt, rest)),
                );
                Low::Let(
                    ax,
                    Expr::Project(ty.clone(), arg, 0),
                    Box::new(x.pass_args(lctx, ax, xt, rest)),
                )
            }
            _ => todo!("{:?}", self),
        }
    }

    pub fn cps_ty(&self, lctx: &LCtx) -> Ty {
        match self
            .cloned(&mut Cloner::new(lctx))
            .normal(&mut lctx.ectx.clone())
        {
            Elab::Unit => Ty::Unit,
            Elab::Builtin(Builtin::Int) => Ty::Int(32),
            Elab::Fun(_, _, _) => Ty::Fun,
            Elab::Binder(_, t) => t.cps_ty(lctx),
            Elab::Type(_) => Ty::Int(64),
            Elab::Var(_, v, _) => Ty::Dyn(
                lctx.get(v)
                    .unwrap_or_else(|| panic!("Not found: {}", v.pretty(lctx).ansi_string())),
            ),
            Elab::Pair(a, b) => Ty::Struct(vec![a.cps_ty(lctx), b.cps_ty(lctx)]),
            Elab::StructInline(v) => {
                let mut v: Vec<_> = v.iter().map(|(x, t)| (x, t.cps_ty(lctx))).collect();
                // Structs are always sorted by field RawSym
                // TODO This isn't stable across separately compiled files, so when we add that we'll need to change
                v.sort_by_key(|(x, _)| x.raw());
                Ty::Struct(v.into_iter().map(|(_, t)| t).collect())
            }
            Elab::StructIntern(s) => ScopeId::Struct(s, Box::new(lctx.scope()))
                .inline(lctx)
                .cps_ty(lctx),
            ty @ Elab::App(_, _) | ty @ Elab::Data(_, _, _) => {
                if let Some(v) = ty.valid_cons(lctx) {
                    let v: Vec<_> = v
                        .into_iter()
                        .map(|(_cons, cons_ty, metas)| {
                            let mut lctx = lctx.clone();
                            for (k, v) in metas {
                                lctx.ectx.set_val(k, v);
                            }
                            let args: Vec<_> =
                                cons_ty.args_iter().map(|x| x.cps_ty(&lctx)).collect();
                            Ty::Struct(args)
                        })
                        .collect();
                    if v.is_empty() {
                        panic!("Empty type {} not allowed!", ty.pretty(lctx).ansi_string())
                    } else {
                        let tag_bits = tag_width(&v);
                        Ty::Struct(vec![Ty::Int(tag_bits), Ty::Union(v)])
                    }
                } else {
                    Ty::Unknown
                }
            }
            _ => todo!("type for '{:?}'", self),
        }
    }

    /// Generates LowIR code that generates Low IR for evaluating this Elab, setting the result to `name`, then running `rest`.
    pub fn cps(&self, name: Val, lctx: &mut LCtx, rest: Low) -> Low {
        match self {
            Elab::Unit => Low::Let(name, Expr::Unit, Box::new(rest)),
            Elab::I32(i) => Low::Let(name, i.into(), Box::new(rest)),
            Elab::Builtin(Builtin::Int) => Low::Let(name, Expr::IntConst(64, 4), Box::new(rest)),
            Elab::Data(_, _, t) => {
                Low::Let(
                    name,
                    // Data types are always dynamically sized, for now at least
                    t.args_iter()
                        .reversed()
                        .fold(
                            (Expr::IntConst(64, -1i64 as u64), Ty::Int(64)),
                            |(ret_val, ret_ty), arg_ty| {
                                let arg_ty = arg_ty.cps_ty(lctx);
                                let arg = lctx.next_val(arg_ty.clone());
                                let cont = lctx.next_val(Ty::Cont);
                                let val = lctx.next_val(ret_ty.clone());
                                (
                                    Expr::Fun {
                                        arg,
                                        arg_ty,
                                        cont,
                                        upvalues: Vec::new(),
                                        body: Box::new(Low::Let(
                                            val,
                                            ret_val,
                                            Box::new(Low::ContCall(cont, ret_ty, val)),
                                        )),
                                    },
                                    Ty::Fun,
                                )
                            },
                        )
                        .0,
                    Box::new(rest),
                )
            }
            Elab::Cons(id, t) => {
                let mut arg_tys = Vec::new();
                let mut arg_vals = Vec::new();
                for ty in t.args_iter() {
                    let cps_ty = ty.cps_ty(lctx);
                    let val = lctx.next_val(cps_ty.clone());
                    // Since any argument's type could depend on previous arguments, it's important to do this in order
                    match ty {
                        Elab::Binder(x, _) => {
                            lctx.set(*x, val);
                        }
                        _ => (),
                    }
                    arg_tys.push(cps_ty);
                    arg_vals.push(val);
                }
                let ret_ty = t.result().cps_ty(lctx);

                if arg_tys.is_empty() {
                    // We're returning the constructed value directly
                    let valid_cons = t.result().valid_cons(lctx).unwrap();
                    let idx = valid_cons
                        .iter()
                        .enumerate()
                        .find(|(_, (tid, _, _))| tid == id)
                        .unwrap()
                        .0;
                    let s_ty = Ty::Struct(arg_tys.clone());
                    let s_val = lctx.next_val(s_ty);
                    let u_ty = match &ret_ty {
                        Ty::Struct(v) => v[1].clone(),
                        _ => panic!("maybe there's only one variant?"),
                    };
                    let u_val = lctx.next_val(u_ty.clone());
                    let tag_bits = tag_width(&valid_cons);
                    let tag_val = lctx.next_val(Ty::Int(tag_bits));

                    Low::Let(
                        s_val,
                        Expr::Struct(Vec::new()),
                        Box::new(Low::Let(
                            u_val,
                            Expr::Variant(u_ty.clone(), s_val, idx as u32),
                            Box::new(Low::Let(
                                tag_val,
                                Expr::IntConst(tag_bits, idx as u64),
                                Box::new(Low::Let(
                                    name,
                                    Expr::Struct(vec![(tag_val, Ty::Int(tag_bits)), (u_val, u_ty)]),
                                    Box::new(rest),
                                )),
                            )),
                        )),
                    )
                } else {
                    // We're returning a function that constructs the value
                    let final_cont = lctx.next_val(Ty::Cont);
                    let body = {
                        let ret_val = lctx.next_val(ret_ty.clone());
                        let valid_cons = t.result().valid_cons(lctx).unwrap();
                        let idx = valid_cons
                            .iter()
                            .enumerate()
                            .find(|(_, (tid, _, _))| tid == id)
                            .unwrap()
                            .0;
                        let s_ty = Ty::Struct(arg_tys.clone());
                        let s_val = lctx.next_val(s_ty);
                        let u_ty = match &ret_ty {
                            Ty::Struct(v) => v[1].clone(),
                            _ => panic!("maybe there's only one variant?"),
                        };
                        let u_val = lctx.next_val(u_ty.clone());
                        let tag_bits = tag_width(&valid_cons);
                        let tag_val = lctx.next_val(Ty::Int(tag_bits));

                        Low::Let(
                            s_val,
                            Expr::Struct(
                                arg_vals
                                    .iter()
                                    .copied()
                                    .zip(arg_tys.iter().cloned())
                                    .collect(),
                            ),
                            Box::new(Low::Let(
                                u_val,
                                Expr::Variant(u_ty.clone(), s_val, idx as u32),
                                Box::new(Low::Let(
                                    tag_val,
                                    Expr::IntConst(tag_bits, idx as u64),
                                    Box::new(Low::Let(
                                        ret_val,
                                        Expr::Struct(vec![
                                            (tag_val, Ty::Int(tag_bits)),
                                            (u_val, u_ty),
                                        ]),
                                        Box::new(Low::ContCall(
                                            final_cont,
                                            ret_ty.clone(),
                                            ret_val,
                                        )),
                                    )),
                                )),
                            )),
                        )
                    };

                    let (body, ret_cont) = arg_vals
                        .iter()
                        .copied()
                        .zip(arg_tys.iter().cloned())
                        .enumerate()
                        .rfold((body, final_cont), |(body, cont), (i, (arg, arg_ty))| {
                            // Here, `cont` is the cont that `body` passes its result to, but it hasn't been defined

                            let next_cont = lctx.next_val(Ty::Cont);
                            let fun_val = lctx.next_val(Ty::Fun);
                            let body = Low::Let(
                                fun_val,
                                Expr::Fun {
                                    arg,
                                    arg_ty,
                                    cont,
                                    body: Box::new(body),
                                    // All args from before this need to be passed through
                                    upvalues: arg_vals
                                        .iter()
                                        .copied()
                                        .zip(arg_tys.iter().cloned())
                                        .take(i)
                                        .collect(),
                                },
                                Box::new(Low::ContCall(next_cont, Ty::Fun, fun_val)),
                            );
                            (body, next_cont)
                        });

                    let rest_cont = make_cont(name, Ty::Fun, lctx, rest);

                    Low::Let(ret_cont, rest_cont, Box::new(body))
                }
            }
            Elab::Pair(x, y) => {
                let xt = x.get_type(lctx).cps_ty(lctx);
                let yt = y.get_type(lctx).cps_ty(lctx);
                let xv = lctx.next_val(xt.clone());
                let yv = lctx.next_val(yt.clone());
                let rest = Low::Let(name, Expr::Struct(vec![(xv, xt), (yv, yt)]), Box::new(rest));
                let rest = y.cps(yv, lctx, rest);
                x.cps(xv, lctx, rest)
            }
            Elab::Project(r, m) => {
                let tr = r.get_type(lctx);
                match &tr {
                    Elab::StructInline(v) => {
                        let mut v: Vec<_> = v.iter().map(|(x, _)| x.raw()).collect();
                        v.sort();
                        if let Ok(idx) = v.binary_search(m) {
                            let tr = tr.cps_ty(lctx);
                            let vr = lctx.next_val(tr.clone());
                            r.cps(
                                vr,
                                lctx,
                                Low::Let(name, Expr::Project(tr, vr, idx as u32), Box::new(rest)),
                            )
                        } else {
                            panic!(
                                "{} doesn't contain {}",
                                r.pretty(lctx).ansi_string(),
                                m.pretty(lctx).ansi_string()
                            );
                        }
                    }
                    _ => panic!("not a struct: {}", r.pretty(lctx).ansi_string()),
                }
            }
            Elab::StructInline(iv) => {
                // Compile it in "struct mode": all members are local variables
                let mut iv: Vec<_> = iv.iter().collect();
                iv.sort_by_key(|(x, _)| x.raw());

                let mut rv = Vec::new();
                let mut vals = Vec::new();
                for (sym, val) in iv {
                    let ty = val.get_type(lctx).cps_ty(lctx);
                    let name = lctx.next_val(ty.clone());
                    lctx.set(*sym, name);
                    rv.push((name, ty));
                    vals.push((name, val));
                }

                let rest = Low::Let(name, Expr::Struct(rv), Box::new(rest));
                vals.into_iter()
                    .rfold(rest, |rest, (name, val)| val.cps(name, lctx, rest))
            }
            Elab::StructIntern(id) => {
                let scope = ScopeId::Struct(*id, Box::new(lctx.scope()));

                // Compile it in "module mode": all members are global functions, like top-level definitions
                let mut rv: Vec<(RawSym, Val, String, Ty)> = Vec::new();
                let s = lctx.database().symbols(scope.clone());
                for sym in s.iter() {
                    // declare void @name(i8* %sp, i8* %k)
                    let global = lctx.database().mangle(scope.clone(), **sym).unwrap();
                    let ty = lctx
                        .database()
                        .elab(scope.clone(), **sym)
                        .unwrap()
                        .get_type(lctx)
                        .cps_ty(lctx);
                    let name = lctx.next_val(ty.clone());
                    lctx.set(**sym, name);
                    rv.push((sym.raw(), name, global, ty));
                }
                rv.sort_by_key(|(x, _, _, _)| *x);

                // Chain continuations through each member, then make the struct and pass it to `rest`
                let mut rest = Low::Let(
                    name,
                    Expr::Struct(rv.iter().map(|(_, k, _, t)| (*k, t.clone())).collect()),
                    Box::new(rest),
                );
                for (_, name, global, ty) in rv {
                    let cont = lctx.next_val(Ty::Cont);
                    let cont_expr = make_cont(name, ty, lctx, rest);
                    rest = Low::Let(cont, cont_expr, Box::new(Low::Global(global, cont)));
                }
                rest
            }
            Elab::CaseOf(val, cases, ret_ty) => {
                let val_ty = val.get_type(lctx).normal(&mut lctx.ectx.clone());

                let val_ty_cps = val_ty.cps_ty(lctx);
                let ret_ty_cps = ret_ty.cps_ty(lctx);
                let val_val = lctx.next_val(val_ty_cps.clone());

                // The branches are going to share rest, so make a cont for it
                let vrest = lctx.next_val(Ty::Cont);
                let crest = make_cont(name, ret_ty_cps.clone(), lctx, rest);

                let rest = cases.iter().rfold(Low::Unreachable, |rest, (pat, body)| {
                    let mut lctx = lctx.clone();

                    for (i, t) in pat.bound() {
                        let t = t.cps_ty(&lctx);
                        let v = lctx.next_val(t);
                        lctx.set(i, v);
                    }

                    let body_result_val = lctx.next_val(ret_ty_cps.clone());
                    let body = body.cps(
                        body_result_val,
                        &mut lctx,
                        Low::ContCall(vrest, ret_ty_cps.clone(), body_result_val),
                    );

                    pat.lower(&val_ty, val_val, &mut lctx, body, rest)
                });

                let rest = Low::Let(vrest, crest, Box::new(rest));

                val.cps(val_val, lctx, rest)
            }
            Elab::Fun(cl, arg, body) => {
                lctx.ectx.add_clos(cl);
                let arg_ty = arg.cps_ty(lctx);
                let argv = lctx.next_val(arg_ty.clone());
                for (i, t) in arg.bound() {
                    let t = t.cps_ty(lctx);
                    let v = lctx.next_val(t);
                    lctx.set(i, v);
                }
                let cont = lctx.next_val(Ty::Cont);
                let body = {
                    let ret = body
                        .get_type(lctx)
                        .normal(&mut lctx.ectx.clone())
                        .cps_ty(lctx);
                    let retv = lctx.next_val(ret.clone());
                    let body = body.cps(retv, lctx, Low::ContCall(cont, ret, retv));
                    Box::new(arg.pass_args(lctx, argv, &arg_ty, body))
                };
                let mut upvalues = cl
                    .tys
                    .iter()
                    .filter(|(k, _)| !lctx.ectx.vals.contains_key(k))
                    .filter_map(|(k, t)| Some((lctx.get(*k)?, t.cps_ty(lctx))))
                    .collect();
                order_upvalues(&mut upvalues, lctx);
                Low::Let(
                    name,
                    Expr::Fun {
                        arg: argv,
                        arg_ty,
                        cont,
                        body,
                        upvalues,
                    },
                    Box::new(rest),
                )
            }
            Elab::App(f, x) => {
                let ty = self
                    .get_type_rec(lctx)
                    .normal(&mut lctx.ectx.clone())
                    .cps_ty(lctx);
                let tx = x.get_type_rec(lctx).cps_ty(lctx);
                let nf = lctx.next_val(Ty::Fun);
                let nx = lctx.next_val(tx.clone());
                let cont = lctx.next_val(Ty::Cont);
                let cont_expr = make_cont(name, ty, lctx, rest);

                let x = x.cps(
                    nx,
                    lctx,
                    Low::Let(cont, cont_expr, Box::new(Low::Call(nf, tx, nx, cont))),
                );
                f.cps(nf, lctx, x)
            }
            Elab::Block(v) => {
                // We need to define them all first, since we actually lower them in reverse order
                let vals: Vec<_> = v
                    .iter()
                    .map(|s| match s {
                        ElabStmt::Def(s, x) => {
                            let t = x.get_type(lctx).cps_ty(lctx);
                            let v = lctx.next_val(t);
                            lctx.set(*s, v);
                            Some(v)
                        }
                        ElabStmt::Expr(_) => None,
                    })
                    .collect();
                v.iter()
                    .zip(vals)
                    .enumerate()
                    .rfold(rest, |rest, (i, (s, val))| match s {
                        ElabStmt::Def(_, x) => {
                            let val = val.unwrap();
                            x.cps(val, lctx, rest)
                        }
                        ElabStmt::Expr(e) => {
                            if i + 1 == v.len() {
                                e.cps(name, lctx, rest)
                            } else {
                                let t = e.get_type(lctx).cps_ty(lctx);
                                let val = lctx.next_val(t);
                                e.cps(val, lctx, rest)
                            }
                        }
                    })
            }
            Elab::Builtin(x) if x.is_binop() => {
                let op = x.int_op().unwrap();
                let arg = lctx.next_val(Ty::Int(32));
                let arg2 = lctx.next_val(Ty::Int(32));
                let cont = lctx.next_val(Ty::Cont);
                let cont2 = lctx.next_val(Ty::Cont);
                let fun2 = lctx.next_val(Ty::Fun);
                let r = lctx.next_val(Ty::Int(32));
                Low::Let(
                    name,
                    Expr::Fun {
                        arg,
                        arg_ty: Ty::Int(32),
                        cont,
                        upvalues: vec![],
                        body: Box::new(Low::Let(
                            fun2,
                            Expr::Fun {
                                arg: arg2,
                                arg_ty: Ty::Int(32),
                                cont: cont2,
                                upvalues: vec![(arg, Ty::Int(32))],
                                body: Box::new(Low::Let(
                                    r,
                                    Expr::IntOp(arg, op, arg2),
                                    Box::new(Low::ContCall(cont2, Ty::Int(32), r)),
                                )),
                            },
                            Box::new(Low::ContCall(cont, Ty::Fun, fun2)),
                        )),
                    },
                    Box::new(rest),
                )
            }
            Elab::Var(_, s, t) => {
                if let Some(v) = lctx.get(*s) {
                    Low::Let(name, Expr::Val(v), Box::new(rest))
                } else {
                    // declare void @name(i8* %sp, i8* %k)
                    let global = lctx.database().mangle(lctx.scope(), *s).unwrap_or_else(|| {
                        panic!(
                            "Not found: {} in scope {:?}",
                            s.pretty(lctx).ansi_string(),
                            lctx.scope()
                        )
                    });
                    let cont = lctx.next_val(Ty::Cont);
                    let cont_expr = make_cont(name, t.cps_ty(lctx), lctx, rest);
                    Low::Let(cont, cont_expr, Box::new(Low::Global(global, cont)))
                }
            }
            _ => todo!("lowering for '{}'", self.pretty(lctx).ansi_string()),
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd)]
pub enum FunAttr {
    AlwaysInline,
    Private,
}

/// A binary integer math operation
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
    BitAnd,
    BitOr,
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum CompOp {
    Eq,
}

impl Builtin {
    pub fn int_op(self) -> Option<IntOp> {
        match self {
            Builtin::Add => Some(IntOp::Add),
            Builtin::Sub => Some(IntOp::Sub),
            Builtin::Mul => Some(IntOp::Mul),
            Builtin::Div => Some(IntOp::Div),
            _ => None,
        }
    }
}
