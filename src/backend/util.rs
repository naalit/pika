//! This mostly has things like printing and typechecking for Low IR
use super::low::*;
use crate::common::*;

#[derive(Default)]
struct CheckCtx {
    tys: HashMap<Val, Ty>,
}
impl CheckCtx {
    fn ty(&self, v: Val) -> Result<&Ty, String> {
        self.tys.get(&v).ok_or(format!("{} not found", v))
    }
}

impl Ty {
    fn typeck(&self, ctx: &CheckCtx) -> Result<(), String> {
        match self {
            Ty::Fun | Ty::Cont | Ty::Int(_) | Ty::Unit => Ok(()),
            Ty::Struct(v) | Ty::Union(v) => {
                for i in v {
                    i.typeck(ctx)?;
                }
                Ok(())
            }
            Ty::Dyn(v) => match ctx.ty(*v)? {
                Ty::Int(64) => Ok(()),
                ty => Err(format!(
                    "required type u64 for type size but got {}: {}",
                    v,
                    ty.pretty().ansi_string()
                )),
            },
        }
    }
}

impl Expr {
    fn typeck(&self, ctx: &CheckCtx) -> Result<Ty, String> {
        match self {
            Expr::Unit => Ok(Ty::Unit),
            Expr::IntConst(size, _) => Ok(Ty::Int(*size)),
            Expr::IntOp(a, _, b) => {
                let ta = ctx.ty(*a)?;
                let tb = ctx.ty(*b)?;
                match &ta {
                    Ty::Int(_) => {
                        if ta == tb {
                            Ok(ta.clone())
                        } else {
                            Err(format!(
                                "non-matching argument types to int op: '{}: {}' and '{}: {}'",
                                a,
                                ta.pretty().ansi_string(),
                                b,
                                tb.pretty().ansi_string()
                            ))
                        }
                    }
                    _ => Err(format!(
                        "only integer types are allowed for int op args, got: {}: {}",
                        a,
                        ta.pretty().ansi_string()
                    )),
                }
            }
            Expr::CompOp(a, _, b) => {
                let ta = ctx.ty(*a)?;
                let tb = ctx.ty(*b)?;
                match &ta {
                    Ty::Int(_) => {
                        if ta == tb {
                            // `CompOp`s return booleans (`i1`)
                            Ok(Ty::Int(1))
                        } else {
                            Err(format!(
                                "non-matching argument types to comp op: '{}: {}' and '{}: {}'",
                                a,
                                ta.pretty().ansi_string(),
                                b,
                                tb.pretty().ansi_string()
                            ))
                        }
                    }
                    _ => Err(format!(
                        "only integer types are allowed for comp op args, got: {}: {}",
                        a,
                        ta.pretty().ansi_string()
                    )),
                }
            }
            Expr::Struct(iv) => {
                let mut rv = Vec::new();
                for (v, t) in iv {
                    t.typeck(ctx)?;
                    if ctx.ty(*v)? != t {
                        return Err(format!(
                            "struct member's actual type {}: {} didn't match given type {}",
                            v,
                            ctx.ty(*v)?.pretty().ansi_string(),
                            t.pretty().ansi_string()
                        ));
                    }
                    rv.push(t.clone());
                }
                Ok(Ty::Struct(rv))
            }
            Expr::Project(t, s, m) => {
                t.typeck(ctx)?;
                if ctx.ty(*s)? != t {
                    return Err(format!(
                        "project lhs's type {}: {} didn't match given type {}",
                        s,
                        ctx.ty(*s)?.pretty().ansi_string(),
                        t.pretty().ansi_string()
                    ));
                }
                if let Ty::Struct(v) = t {
                    if let Some(t) = v.get(*m as usize) {
                        Ok(t.clone())
                    } else {
                        Err(format!(
                            "project {} out of range for struct type {}: {}",
                            m,
                            s,
                            t.pretty().ansi_string()
                        ))
                    }
                } else {
                    Err(format!(
                        "project's lhs must be struct type, got {}: {}",
                        s,
                        t.pretty().ansi_string()
                    ))
                }
            }
            Expr::Variant(t, val, i) => {
                t.typeck(ctx)?;
                if let Ty::Union(v) = t {
                    if let Some(m_t) = v.get(*i as usize) {
                        if ctx.ty(*val)? != m_t {
                            Err(format!(
                                "variant's argument {}: {} doesn't match variant {} type {}",
                                val,
                                ctx.ty(*val)?.pretty().ansi_string(),
                                i,
                                m_t.pretty().ansi_string()
                            ))
                        } else {
                            Ok(t.clone())
                        }
                    } else {
                        Err(format!(
                            "variant {} out of range for union type {}",
                            i,
                            t.pretty().ansi_string()
                        ))
                    }
                } else {
                    Err(format!(
                        "variant's type must be a union, got {}",
                        t.pretty().ansi_string()
                    ))
                }
            }
            Expr::AsVariant(t, u, i) => {
                t.typeck(ctx)?;
                if ctx.ty(*u)? != t {
                    return Err(format!(
                        "as-variant lhs's type {}: {} didn't match given type {}",
                        u,
                        ctx.ty(*u)?.pretty().ansi_string(),
                        t.pretty().ansi_string()
                    ));
                }
                if let Ty::Union(v) = t {
                    if let Some(t) = v.get(*i as usize) {
                        Ok(t.clone())
                    } else {
                        Err(format!(
                            "as-variant {} out of range for union type {}: {}",
                            i,
                            u,
                            t.pretty().ansi_string()
                        ))
                    }
                } else {
                    Err(format!(
                        "as-variant's type must be a union, got {}: {}",
                        u,
                        t.pretty().ansi_string()
                    ))
                }
            }
            Expr::Val(v) => ctx.ty(*v).map(Ty::clone),
            Expr::Cont {
                arg,
                arg_ty,
                body,
                upvalues,
            } => {
                if arg_ty == &Ty::Cont {
                    return Err(format!("continuations can't take continuation arguments, it would break stack semantics: {}", arg));
                }
                let mut nctx = CheckCtx::default();
                for (v, t) in upvalues {
                    t.typeck(&nctx)?;
                    if ctx.ty(*v)? != t {
                        return Err(format!(
                            "upvalue type {}: {} didn't match actual type {}",
                            v,
                            ctx.ty(*v)?.pretty().ansi_string(),
                            t.pretty().ansi_string()
                        ));
                    }
                    nctx.tys.insert(*v, t.clone());
                }
                arg_ty.typeck(&nctx)?;
                nctx.tys.insert(*arg, arg_ty.clone());
                body.typeck(&mut nctx)?;
                Ok(Ty::Cont)
            }
            Expr::Fun {
                arg,
                arg_ty,
                cont,
                body,
                upvalues,
            } => {
                let mut nctx = CheckCtx::default();
                for (v, t) in upvalues {
                    t.typeck(&nctx)?;
                    if ctx.ty(*v)? != t {
                        return Err(format!(
                            "upvalue type {}: {} didn't match actual type {}",
                            v,
                            ctx.ty(*v)?.pretty().ansi_string(),
                            t.pretty().ansi_string()
                        ));
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
    fn typeck(&self, ctx: &mut CheckCtx) -> Result<(), String> {
        match self {
            Low::Let(k, v, rest) => {
                let t = v.typeck(ctx)?;
                ctx.tys.insert(*k, t);
                rest.typeck(ctx)
            }
            Low::Call(f, tx, x, k) => {
                tx.typeck(ctx)?;
                if *ctx.ty(*f)? != Ty::Fun {
                    return Err(format!(
                        "called function must have function type, got {}: {}",
                        f,
                        ctx.ty(*f)?.pretty().ansi_string()
                    ));
                }
                if ctx.ty(*x)? != tx {
                    return Err(format!(
                        "argument's actual type {}: {} didn't match declared type {}",
                        x,
                        ctx.ty(*x)?.pretty().ansi_string(),
                        tx.pretty().ansi_string()
                    ));
                }
                if *ctx.ty(*k)? != Ty::Cont {
                    return Err(format!(
                        "continuation argument must have continuation type, got {}: {}",
                        k,
                        ctx.ty(*k)?.pretty().ansi_string()
                    ));
                }
                Ok(())
            }
            Low::ContCall(k, tx, x) => {
                tx.typeck(ctx)?;
                if *ctx.ty(*k)? != Ty::Cont {
                    return Err(format!(
                        "called continuation must have continuation type, got {}: {}",
                        k,
                        ctx.ty(*k)?.pretty().ansi_string()
                    ));
                }
                if ctx.ty(*x)? != tx {
                    return Err(format!(
                        "argument's actual type {}: {} didn't match declared type {}",
                        x,
                        ctx.ty(*x)?.pretty().ansi_string(),
                        tx.pretty().ansi_string()
                    ));
                }
                Ok(())
            }
            Low::IfElse(cond, yes, no) => {
                if *ctx.ty(*cond)? != Ty::Int(1) {
                    return Err(format!(
                        "if-else condition must be a boolean (i1), got {}: {}",
                        cond,
                        ctx.ty(*cond)?.pretty().ansi_string()
                    ));
                }
                yes.typeck(ctx)?;
                no.typeck(ctx)?;
                Ok(())
            }
            // We assume all globals are defined for now
            Low::Global(_, k) => match ctx.ty(*k)? {
                Ty::Cont => Ok(()),
                ty => Err(format!(
                    "continuation argument to global must be continuation, got {}: {}",
                    k,
                    ty.pretty().ansi_string()
                )),
            },
            Low::Halt(v) => match ctx.ty(*v)? {
                Ty::Int(32) => Ok(()),
                ty => Err(format!(
                    "wrong type for halt, expected i32, got {}: {}",
                    v,
                    ty.pretty().ansi_string()
                )),
            },
            Low::Unreachable => Ok(()),
        }
    }

    /// Typecheck this Low IR, assuming the continuation `cont`
    pub fn type_check(&self, cont: Val) {
        let mut ctx = CheckCtx::default();
        ctx.tys.insert(cont, Ty::Cont);
        match self.typeck(&mut ctx) {
            Ok(()) => {
                if cfg!(feature = "logging") {
                    println!("Low IR typechecked!")
                }
            }
            Err(msg) => panic!("Low IR didn't typecheck: {}", msg),
        }
    }
}

impl SPretty for IntOp {
    fn pretty(&self) -> Doc {
        match self {
            IntOp::Add => Doc::start("+"),
            IntOp::Sub => Doc::start("-"),
            IntOp::Mul => Doc::start("*"),
            IntOp::Div => Doc::start("/"),
            IntOp::BitAnd => Doc::start("&"),
            IntOp::BitOr => Doc::start("|"),
        }
    }
}
impl SPretty for CompOp {
    fn pretty(&self) -> Doc {
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

impl SPretty for Expr {
    fn pretty(&self) -> Doc {
        match self {
            Expr::Unit => Doc::start("()").style(Style::Literal),
            Expr::IntConst(size, i) => Doc::start(i).add("u").add(size).style(Style::Literal),
            Expr::IntOp(a, op, b) => Doc::start(a).space().chain(op.pretty()).space().add(b),
            Expr::CompOp(a, op, b) => Doc::start(a).space().chain(op.pretty()).space().add(b),
            Expr::Val(v) => Doc::start(v),
            Expr::Struct(v) => Doc::start("{")
                .chain(Doc::intersperse(
                    v.iter().map(|(x, t)| t.pretty().space().add(x)),
                    Doc::start(",").space(),
                ))
                .add("}"),
            Expr::Project(_, r, m) | Expr::AsVariant(_, r, m) => Doc::start(r).add(".").add(m),
            Expr::Variant(t, v, m) => t.pretty().add(".").add(m).add("(").add(v).add(")"),
            Expr::Cont {
                arg,
                arg_ty,
                body,
                upvalues,
            } => Doc::start("cont")
                .style(Style::Keyword)
                .add("{")
                .chain(Doc::intersperse(
                    upvalues.iter().map(|(x, t)| t.pretty().space().add(x)),
                    Doc::start(",").space(),
                ))
                .add("}")
                .add("(")
                .chain(arg_ty.pretty())
                .space()
                .add(arg)
                .add(")")
                .space()
                .add("{")
                .line()
                .chain(body.pretty())
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
                    upvalues.iter().map(|(x, t)| t.pretty().space().add(x)),
                    Doc::start(",").space(),
                ))
                .add("}")
                .add("(")
                .chain(arg_ty.pretty())
                .space()
                .add(arg)
                .add(",")
                .space()
                .chain(Ty::Cont.pretty())
                .space()
                .add(cont)
                .add(")")
                .space()
                .add("{")
                .line()
                .chain(body.pretty())
                .indent()
                .line()
                .add("}"),
        }
    }
}
impl SPretty for Ty {
    fn pretty(&self) -> Doc {
        match self {
            Ty::Unit => Doc::start("()").style(Style::Literal),
            Ty::Int(size) => Doc::start("u").add(size).style(Style::Literal),
            Ty::Fun => Doc::start("fun").style(Style::Keyword),
            Ty::Cont => Doc::start("cont").style(Style::Keyword),
            Ty::Struct(v) => Doc::start("struct")
                .style(Style::Keyword)
                .space()
                .add("{")
                .chain(Doc::intersperse(
                    v.iter().map(|x| x.pretty()),
                    Doc::start(",").space(),
                ))
                .add("}"),
            Ty::Union(v) => Doc::start("union")
                .style(Style::Keyword)
                .space()
                .add("{")
                .chain(Doc::intersperse(
                    v.iter().map(|x| x.pretty()),
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
impl SPretty for Low {
    fn pretty(&self) -> Doc {
        match self {
            Low::Let(name, val, rest) => Doc::start("let")
                .style(Style::Keyword)
                .space()
                .add(name)
                .space()
                .add("=")
                .space()
                .chain(val.pretty())
                .space()
                .chain(Doc::start("in").style(Style::Keyword))
                .line()
                .chain(rest.pretty()),
            Low::Call(f, t, x, k) => Doc::start("call")
                .style(Style::Keyword)
                .space()
                .add(f)
                .add("(")
                .chain(t.pretty())
                .space()
                .add(x)
                .add(",")
                .space()
                .chain(Ty::Cont.pretty())
                .space()
                .add(k)
                .add(")"),
            Low::ContCall(k, t, x) => Doc::start("continue")
                .style(Style::Keyword)
                .space()
                .add(k)
                .add("(")
                .chain(t.pretty())
                .space()
                .add(x)
                .add(")"),
            Low::IfElse(cond, yes, no) => Doc::start("if")
                .style(Style::Keyword)
                .space()
                .add(cond)
                .space()
                .chain(Doc::start("then").style(Style::Keyword))
                .line()
                .chain(yes.pretty())
                .indent()
                .line()
                .chain(
                    Doc::start("else")
                        .style(Style::Keyword)
                        .line()
                        .chain(no.pretty())
                        .indent(),
                ),
            Low::Halt(v) => Doc::start("halt").style(Style::Keyword).space().add(v),
            Low::Global(name, k) => Doc::start("call global")
                .style(Style::Keyword)
                .space()
                .add(name)
                .add("(")
                .add(k)
                .add(")"),
            Low::Unreachable => Doc::start("unreachable").style(Style::Keyword),
        }
    }
}
