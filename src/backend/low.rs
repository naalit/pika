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
        cont_ty: Ty,
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

impl Expr {
    pub fn fvs(&self, set: &mut HashSet<Val>) {
        match self {
            Expr::IntConst(_, _) => (),
            Expr::IntOp(a, _, b) => {
                set.insert(*a);
                set.insert(*b);
            }
            Expr::Struct(v) => set.extend(v.iter().map(|(x, _)| *x)),
            Expr::Project(_, r, _) => {
                set.insert(*r);
            }
            Expr::Val(v) => {
                set.insert(*v);
            }
            // Closures essentially have this precomputed
            Expr::Cont { upvalues, .. } | Expr::Fun { upvalues, .. } => {
                for (i, _) in upvalues {
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

impl Elab {
    pub fn pass_args(&self, lctx: &mut LCtx, arg: Val, ty: &Ty, rest: Low) -> Low {
        match self {
            Elab::Builtin(Builtin::Int) | Elab::Type(_) | Elab::Var(_, _, _) => rest,
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
                    Box::new(y.pass_args(lctx, arg, yt, rest)),
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
        match self {
            Elab::Builtin(Builtin::Int) => Ty::Int(32),
            Elab::Fun(_, _, _) => Ty::Fun,
            Elab::Binder(_, t) => t.cps_ty(lctx),
            Elab::Type(_) => Ty::Int(64),
            Elab::Var(_, v, _) => Ty::Dyn(
                lctx.get(*v)
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
                let arg_ty = arg.cps_ty(lctx);
                let argv = lctx.next_val(arg_ty.clone());
                for (i, t) in arg.bound() {
                    let t = t.cps_ty(lctx);
                    let v = lctx.next_val(t);
                    lctx.set(i, v);
                }
                let cont = lctx.next_val(Ty::Cont);
                lctx.ectx.add_clos(cl);
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
                        cont_ty: Ty::Cont,
                        body,
                        upvalues: cl
                            .tys
                            .iter()
                            .map(|(x, t)| (lctx.get(*x).unwrap(), t.cps_ty(lctx)))
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
                // We need to pass everything `rest` uses to the continuation
                let mut upvalues = rest.fvs();
                upvalues.remove(&name);
                let upvalues = upvalues
                    .into_iter()
                    .map(|x| (x, lctx.tys.get(&x).unwrap().clone()))
                    .collect();
                let x = x.cps(
                    nx,
                    lctx,
                    Low::Let(
                        cont,
                        Expr::Cont {
                            arg: name,
                            arg_ty: ty,
                            body: Box::new(rest),
                            upvalues,
                        },
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
                        cont_ty: Ty::Cont,
                        upvalues: vec![],
                        body: Box::new(Low::Let(
                            fun2,
                            Expr::Fun {
                                arg: arg2,
                                arg_ty: Ty::Int(32),
                                cont: cont2,
                                cont_ty: Ty::Cont,
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
                    // We need to pass everything `rest` uses to the continuation
                    let mut upvalues = rest.fvs();
                    upvalues.remove(&name);
                    let upvalues = upvalues
                        .into_iter()
                        .map(|x| (x, lctx.tys.get(&x).unwrap().clone()))
                        .collect();
                    Low::Let(
                        cont,
                        Expr::Cont {
                            arg: name,
                            arg_ty: t.cps_ty(lctx),
                            upvalues,
                            body: Box::new(rest),
                        },
                        Box::new(Low::Global(global, cont)),
                    )
                }
            }
            _ => todo!("{}", self.pretty(lctx).ansi_string()),
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
                cont_ty,
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
                .chain(cont_ty.pretty(ctx))
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
