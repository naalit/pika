use crate::{common::*, term::Builtin};
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
    Int(u32),
    Fun,  //(/*Box<Ty>, */Box<Ty>),
    Cont, //(Box<Ty>),
    Struct(Vec<Ty>),
    /// Used for unknown types; represents a location on the stack, with a size
    Dyn(Val),
}

/// A primitive expression, that actually returns a value
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    IntConst(u32, u64),
    IntOp(Val, IntOp, Val),
    Struct(Vec<(Val, Ty)>),
    Project(Ty, Val, u32),
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
        // There really should be a better way of doing this
        Expr::IntConst(32, unsafe { std::mem::transmute::<i32, u32>(i) } as u64)
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
    Halt(Val),
}

pub struct LCtx<'a> {
    to_val: HashMap<Sym, Val>,
    tys: HashMap<Val, Ty>,
    ectx: ECtx<'a>,
}
impl<'a> LCtx<'a> {
    pub fn next_val(&mut self, t: Ty) -> Val {
        let v = next_val();
        self.tys.insert(v, t);
        v
    }

    fn get(&self, x: Sym) -> Option<Val> {
        self.to_val.get(&x).copied()
    }

    fn set(&mut self, x: Sym, v: Val) {
        self.to_val.insert(x, v);
    }
}
impl<'a> Clone for LCtx<'a> {
    fn clone(&self) -> Self {
        LCtx {
            to_val: self.to_val.clone(),
            tys: HashMap::new(),
            ectx: self.ectx.clone(),
        }
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
    fn database(&self) -> &dyn MainGroupP {
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
            Ty::Int(_)
            |Ty::Fun
            |Ty::Cont
            |Ty::Struct(_) => {}
        }
    }
}

impl Expr {
    pub fn fvs(&self, set: &mut HashSet<Val>) {
        match self {
            Expr::IntConst(_, _) => (),
            Expr::IntOp(a, _, b) => {
                set.insert(*a);
                set.insert(*b);
            }
            Expr::Struct(v) => set.extend(v.iter().map(|(x, _)| *x)),
            Expr::Project(t, r, _) => {
                t.fvs(set);
                set.insert(*r);
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
        }
    }
}

// Figures out the necessary upvalues, etc. to turn `rest` into a continuation you can pass around and call
fn make_cont(arg: Val, arg_ty: Ty, lctx: &LCtx, rest: Low) -> Expr {
    // We need to pass everything `rest` uses to the continuation
    let mut upvalues = rest.fvs();
    // The argument type might depend on something
    arg_ty.fvs(&mut upvalues);
    upvalues.remove(&arg);
    let mut upvalues: Vec<_> = upvalues
        .into_iter()
        .map(|x| (x, lctx.tys.get(&x).unwrap().clone()))
        .collect();

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

        upvalues.extend(extra.into_iter()
            .map(|x| (x, lctx.tys.get(&x).unwrap().clone())));
        i += 1;
    }
    // And here we reverse it so dependencies are in the right order
    upvalues.reverse();

    Expr::Cont {
        arg,
        arg_ty,
        body: Box::new(rest),
        upvalues,
    }
}

impl Elab {
    pub fn pass_args(&self, lctx: &mut LCtx, arg: Val, ty: &Ty, rest: Low) -> Low {
        match self {
            // These are types that don't bind anything
            Elab::Builtin(Builtin::Int) | Elab::Type(_) | Elab::Var(_, _, _) | Elab::Fun(_, _, _) => rest,
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
        match self.cloned(&mut Cloner::new(lctx)).normal(&mut lctx.ectx.clone()) {
            Elab::Builtin(Builtin::Int) => Ty::Int(32),
            Elab::Fun(_, _, _) => Ty::Fun,
            Elab::Binder(_, t) => t.cps_ty(lctx),
            Elab::Type(_) => Ty::Int(64),
            Elab::Var(_, v, _) => Ty::Dyn(
                lctx.get(v)
                    .unwrap_or_else(|| panic!("Not found: {}", v.pretty(lctx).ansi_string())),
            ),
            Elab::Pair(a, b) => Ty::Struct(vec![a.cps_ty(lctx), b.cps_ty(lctx)]),
            _ => todo!("{:?}", self),
        }
    }

    /// Generates LowIR code that generates Low IR for evaluating this Elab, setting the result to `name`, then running `rest`.
    pub fn cps(&self, name: Val, lctx: &mut LCtx, rest: Low) -> Low {
        match self {
            Elab::I32(i) => Low::Let(name, i.into(), Box::new(rest)),
            Elab::Builtin(Builtin::Int) => Low::Let(name, Expr::IntConst(64, 4), Box::new(rest)),
            Elab::Pair(x, y) => {
                let xt = x.get_type(lctx).cps_ty(lctx);
                let yt = y.get_type(lctx).cps_ty(lctx);
                let xv = lctx.next_val(xt.clone());
                let yv = lctx.next_val(yt.clone());
                let rest = Low::Let(name, Expr::Struct(vec![(xv, xt), (yv, yt)]), Box::new(rest));
                let rest = y.cps(yv, lctx, rest);
                x.cps(xv, lctx, rest)
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
                Low::Let(
                    name,
                    Expr::Fun {
                        arg: argv,
                        arg_ty,
                        cont,
                        body,
                        upvalues: cl
                            .tys
                            .iter()
                            .filter(|(k, _)| !lctx.ectx.vals.contains_key(k))
                            .map(|(k, t)| (lctx.get(*k).unwrap_or_else(|| panic!("Not found: upvalue {}", k.pretty(lctx).ansi_string())), t.cps_ty(lctx)))
                            .collect(),
                    },
                    Box::new(rest),
                )
            }
            Elab::App(f, x) => {
                let ty = self
                    .get_type(lctx)
                    .normal(&mut lctx.ectx.clone())
                    .cps_ty(lctx);
                let tx = x.get_type(lctx).cps_ty(lctx);
                let nf = lctx.next_val(Ty::Fun);
                let nx = lctx.next_val(tx.clone());
                let cont = lctx.next_val(Ty::Cont);
                let cont_expr = make_cont(name, ty, lctx, rest);

                let x = x.cps(
                    nx,
                    lctx,
                    Low::Let(
                        cont,
                        cont_expr,
                        Box::new(Low::Call(nf, tx, nx, cont)),
                    ),
                );
                f.cps(nf, lctx, x)
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
                    // declare void @name({ i8*, void (ret_ty)* } %k)
                    let global = lctx.database().mangle(lctx.scope(), *s).unwrap();
                    let cont = lctx.next_val(Ty::Cont);
                    let cont_expr = make_cont(name, t.cps_ty(lctx), lctx, rest);
                    Low::Let(
                        cont,
                        cont_expr,
                        Box::new(Low::Global(global, cont)),
                    )
                }
            }
            _ => todo!("{}", self.pretty(lctx).ansi_string()),
        }
    }
}

#[derive(Default)]
struct CheckCtx {
    tys: HashMap<Val, Ty>,
}
impl CheckCtx {
    fn ty(&self, v: Val) -> Result<&Ty, (&'static str, Val)> {
        self.tys.get(&v).ok_or(("not found", v))
    }
}

impl Ty {
    fn typeck(&self, ctx: &CheckCtx) -> Result<(), (&'static str, Val)> {
        match self {
            Ty::Fun
            | Ty::Cont
            | Ty::Int(_) => Ok(()),
            Ty::Struct(v) => {
                for i in v {
                    i.typeck(ctx)?;
                }
                Ok(())
            }
            Ty::Dyn(v) => match ctx.ty(*v)? {
                Ty::Int(64) => Ok(()),
                _ => Err(("required type u64 for type size", *v)),
            }
        }
    }
}

impl Expr {
    fn typeck(&self, ctx: &CheckCtx) -> Result<Ty, (&'static str, Val)> {
        match self {
            Expr::IntConst(size, _) => Ok(Ty::Int(*size)),
            Expr::IntOp(a, _, b) => {
                let ta = ctx.ty(*a)?;
                let tb = ctx.ty(*b)?;
                match &ta {
                    Ty::Int(_) => if ta == tb {
                        Ok(ta.clone())
                    } else {
                        Err(("non-matching argument types to int op", *b))
                    },
                    _ => Err(("only integer types are allowed for int op args", *a)),
                }
            }
            Expr::Struct(iv) => {
                let mut rv = Vec::new();
                for (v, t) in iv {
                    t.typeck(ctx)?;
                    if ctx.ty(*v)? != t {
                        return Err(("struct member's actual type didn't match given type", *v));
                    }
                    rv.push(t.clone());
                }
                Ok(Ty::Struct(rv))
            }
            Expr::Project(t, s, m) => {
                t.typeck(ctx)?;
                if ctx.ty(*s)? != t {
                    return Err(("project lhs's type didn't match given type", *s));
                }
                if let Ty::Struct(v) = t {
                    if let Some(t) = v.get(*m as usize) {
                        Ok(t.clone())
                    } else {
                        Err(("project out of range for struct type", *s))
                    }
                } else {
                    Err(("project's lhs must be struct type", *s))
                }
            }
            Expr::Val(v) => ctx.ty(*v).map(Ty::clone),
            Expr::Cont { arg, arg_ty, body, upvalues } => {
                let mut nctx = CheckCtx::default();
                for (v, t) in upvalues {
                    t.typeck(&nctx)?;
                    if ctx.ty(*v)? != t {
                        return Err(("upvalue type didn't match actual type", *v));
                    }
                    nctx.tys.insert(*v, t.clone());
                }
                arg_ty.typeck(&nctx)?;
                nctx.tys.insert(*arg, arg_ty.clone());
                body.typeck(&mut nctx)?;
                Ok(Ty::Cont)
            }
            Expr::Fun { arg, arg_ty, cont, body, upvalues } => {
                let mut nctx = CheckCtx::default();
                for (v, t) in upvalues {
                    t.typeck(&nctx)?;
                    if ctx.ty(*v)? != t {
                        return Err(("upvalue type didn't match actual type", *v));
                    }
                    nctx.tys.insert(*v, t.clone());
                }
                arg_ty.typeck(&nctx)?;
                nctx.tys.insert(*arg, arg_ty.clone());
                nctx.tys.insert(*cont, Ty::Cont);
                body.typeck(&mut nctx)?;
                Ok(Ty::Fun)
            }
        }
    }
}

impl Low {
    fn typeck(&self, ctx: &mut CheckCtx) -> Result<(), (&'static str, Val)> {
        match self {
            Low::Let(k, v, rest) => {
                let t = v.typeck(ctx)?;
                ctx.tys.insert(*k, t);
                rest.typeck(ctx)
            },
            Low::Call(f, tx, x, k) => {
                tx.typeck(ctx)?;
                if *ctx.ty(*f)? != Ty::Fun {
                    return Err(("called function must have function type", *f));
                }
                if ctx.ty(*x)? != tx {
                    return Err(("argument's actual type didn't match declared type", *x));
                }
                if *ctx.ty(*k)? != Ty::Cont {
                    return Err(("continuation argument must have continuation type", *k));
                }
                Ok(())
            },
            Low::ContCall(k, tx, x) => {
                tx.typeck(ctx)?;
                if *ctx.ty(*k)? != Ty::Cont {
                    return Err(("called continuation must have continuation type", *k));
                }
                if ctx.ty(*x)? != tx {
                    return Err(("argument's actual type didn't match declared type", *x));
                }
                Ok(())
            },
            // We assume all globals are defined for now
            Low::Global(_, k) => match ctx.ty(*k)? {
                Ty::Cont => Ok(()),
                _ => Err(("passed to global but not a continuation", *k)),
            },
            Low::Halt(v) => match ctx.ty(*v)? {
                Ty::Int(32) => Ok(()),
                _ => Err(("wrong type for halt", *v)),
            },
        }
    }

    /// Typecheck this Low IR, assuming the continuation `cont`
    pub fn type_check(&self, cont: Val) {
        let mut ctx = CheckCtx::default();
        ctx.tys.insert(cont, Ty::Cont);
        match self.typeck(&mut ctx) {
            Ok(()) => if cfg!(feature = "logging") {
                println!("Low IR typechecked!")
            },
            Err((msg, val)) => panic!("Low IR didn't typecheck: value {}: {}", val, msg),
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
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum CompOp {
    Eq,
}

/// A binary logic operation, used for pattern matching compilation
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum BoolOp {
    And,
    Or,
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

impl Pretty for IntOp {
    fn pretty(&self, _ctx: &impl HasBindings) -> Doc {
        match self {
            IntOp::Add => Doc::start("+"),
            IntOp::Sub => Doc::start("-"),
            IntOp::Mul => Doc::start("*"),
            IntOp::Div => Doc::start("/"),
        }
    }
}
impl Pretty for BoolOp {
    fn pretty(&self, _ctx: &impl HasBindings) -> Doc {
        match self {
            BoolOp::And => Doc::start("&&"),
            BoolOp::Or => Doc::start("||"),
        }
    }
}
impl Pretty for CompOp {
    fn pretty(&self, _ctx: &impl HasBindings) -> Doc {
        match self {
            CompOp::Eq => Doc::start("=="),
        }
    }
}

impl std::fmt::Display for Val {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "%{}", self.num())
    }
}

impl Pretty for Expr {
    fn pretty(&self, ctx: &impl crate::common::HasBindings) -> Doc {
        match self {
            Expr::IntConst(size, i) => Doc::start(i).add("u").add(size),
            Expr::IntOp(a, op, b) => Doc::start(a).space().chain(op.pretty(ctx)).space().add(b),
            Expr::Val(v) => Doc::start(v),
            Expr::Struct(v) => Doc::start("{")
                .chain(Doc::intersperse(
                    v.iter().map(|(x, _)| Doc::start(x)),
                    Doc::start(",").space(),
                ))
                .add("}"),
            Expr::Project(_, r, m) => Doc::start(r).add(".").add(m),
            Expr::Cont {
                arg,
                arg_ty,
                body,
                upvalues,
            } => Doc::start("cont")
                .style(Style::Keyword)
                .add("{")
                .chain(Doc::intersperse(
                    upvalues.iter().map(|(x, t)| t.pretty(ctx).space().add(x)),
                    Doc::start(",").space(),
                ))
                .add("}")
                .add("(")
                .chain(arg_ty.pretty(ctx))
                .space()
                .add(arg)
                .add(")")
                .space()
                .add("{")
                .line()
                .chain(body.pretty(ctx))
                .indent()
                .line()
                .add("}"),
            Expr::Fun {
                arg,
                arg_ty,
                cont,
                body,
                upvalues,
            } => Doc::start("fun")
                .style(Style::Keyword)
                .add("{")
                .chain(Doc::intersperse(
                    upvalues.iter().map(|(x, t)| t.pretty(ctx).space().add(x)),
                    Doc::start(",").space(),
                ))
                .add("}")
                .add("(")
                .chain(arg_ty.pretty(ctx))
                .space()
                .add(arg)
                .add(",")
                .space()
                .chain(Ty::Cont.pretty(ctx))
                .space()
                .add(cont)
                .add(")")
                .space()
                .add("{")
                .line()
                .chain(body.pretty(ctx))
                .indent()
                .line()
                .add("}"),
        }
    }
}
impl Pretty for Ty {
    fn pretty(&self, ctx: &impl crate::common::HasBindings) -> Doc {
        match self {
            Ty::Int(size) => Doc::start("u").add(size).style(Style::Literal),
            Ty::Fun => Doc::start("fun").style(Style::Keyword),
            Ty::Cont => Doc::start("cont").style(Style::Keyword),
            Ty::Struct(v) => Doc::start("{")
                .chain(Doc::intersperse(
                    v.iter().map(|x| x.pretty(ctx)),
                    Doc::start(",").space(),
                ))
                .add("}"),
            Ty::Dyn(v) => Doc::start("dyn")
                .style(Style::Keyword)
                .add("[")
                .add(v)
                .add("]"),
        }
    }
}
impl Pretty for Low {
    fn pretty(&self, ctx: &impl crate::common::HasBindings) -> Doc {
        match self {
            Low::Let(name, val, rest) => Doc::start("let")
                .style(Style::Keyword)
                .space()
                .add(name)
                .space()
                .add("=")
                .space()
                .chain(val.pretty(ctx))
                .space()
                .chain(Doc::start("in").style(Style::Keyword))
                .line()
                .chain(rest.pretty(ctx)),
            Low::Call(f, t, x, k) => Doc::start("call")
                .style(Style::Keyword)
                .space()
                .add(f)
                .add("(")
                .chain(t.pretty(ctx))
                .space()
                .add(x)
                .add(",")
                .space()
                .chain(Ty::Cont.pretty(ctx))
                .space()
                .add(k)
                .add(")"),
            Low::ContCall(k, t, x) => Doc::start("continue")
                .style(Style::Keyword)
                .space()
                .add(k)
                .add("(")
                .chain(t.pretty(ctx))
                .space()
                .add(x)
                .add(")"),
            Low::Halt(v) => Doc::start("halt").style(Style::Keyword).space().add(v),
            Low::Global(name, k) => Doc::start("call global")
                .style(Style::Keyword)
                .space()
                .add(name)
                .add("(")
                .add(k)
                .add(")"),
        }
    }
}
