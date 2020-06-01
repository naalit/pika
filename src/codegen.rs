//! We use Inkwell to generate LLVM.
//! Unfortunately, Inkwell is impossible to integrate with Salsa, for two reasons:
//! - Everything uses lifetimes, and Salsa currently doesn't support those *at all*
//! - Most things aren't thread safe, which Salsa requires
//! So, in Salsa, we convert terms into LowIR, which is supposed to be very close to LLVM.
//! We convert that into LLVM outside of Salsa, and hopefully that requires hardly any work - most should be done in Salsa.

use crate::{
    common::*,
    elab::{Elab, ElabStmt},
    term::Builtin,
};
pub use inkwell::context::Context;
use inkwell::{builder::Builder, module::Module, types::*, values::*};
use std::collections::HashMap;
use std::convert::TryInto;

/// We need one of these to generate any LLVM code, but not to generate LowIR
pub struct CodegenCtx<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    locals: HashMap<Sym, AnyValueEnum<'ctx>>,
}
impl<'ctx> CodegenCtx<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        CodegenCtx {
            context,
            builder: context.create_builder(),
            locals: HashMap::new(),
        }
    }
}

/// A LowIR type
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowTy {
    Int,
    Void,
    /// Maps to an LLVM function pointer type
    Fun(Box<LowTy>, Box<LowTy>),
    /// No distinction between pairs and structs like in the main language
    Struct(Vec<LowTy>),
}
impl LowTy {
    /// Create an LLVM function type that returns `self`
    fn llvm_fn_type<'ctx>(&self, ctx: &'ctx Context, params: &[LowTy]) -> FunctionType<'ctx> {
        let params: Vec<_> = params
            .iter()
            .map(|x| {
                // If we've got Void as a parameter, that means it was an erased type
                // We represent that as a unit parameter, and units are just Bools = false
                // which are actually zero-sized so LLVM dead code elimination should get rid of them
                if let LowTy::Void = x {
                    ctx.bool_type().as_basic_type_enum()
                } else {
                    x.llvm(ctx)
                        .try_into()
                        .expect("Parameter types must be basic!")
                }
            })
            .collect();
        match self {
            LowTy::Int => ctx.i32_type().fn_type(&params, false),
            LowTy::Void => ctx.void_type().fn_type(&params, false),
            LowTy::Fun(from, to) => to
                .llvm_fn_type(ctx, &[(**from).clone()])
                .ptr_type(inkwell::AddressSpace::Generic)
                .fn_type(&params, false),
            LowTy::Struct(v) => ctx
                .struct_type(
                    &v.iter()
                        .map(|a| a.llvm(ctx).try_into().unwrap())
                        .collect::<Vec<_>>(),
                    false,
                )
                .fn_type(&params, false),
        }
    }

    /// Get the LLVM representation of `self`
    fn llvm<'ctx>(&self, ctx: &'ctx Context) -> AnyTypeEnum<'ctx> {
        match self {
            LowTy::Int => AnyTypeEnum::IntType(ctx.i32_type()),
            LowTy::Void => AnyTypeEnum::VoidType(ctx.void_type()),
            LowTy::Fun(from, to) => to
                .llvm_fn_type(ctx, &[(**from).clone()])
                .ptr_type(inkwell::AddressSpace::Generic)
                .into(),
            LowTy::Struct(v) => ctx
                .struct_type(
                    &v.iter()
                        .map(|a| a.llvm(ctx).try_into().unwrap())
                        .collect::<Vec<_>>(),
                    false,
                )
                .as_any_type_enum(),
        }
    }
}
impl Elab {
    fn has_type(&self) -> bool {
        match self {
            Elab::Pair(x, y) => x.has_type() || y.has_type(),
            Elab::Struct(_, v) => v.iter().any(|(_, x)| x.has_type()),
            Elab::Type => true,
            Elab::Unit | Elab::Builtin(_) | Elab::I32(_) | Elab::Var(_, _) => false,
            Elab::Binder(_, t) => t.has_type(),
            Elab::Fun(a, b, _) => a.has_type() || b.has_type(),
            Elab::App(_, _) | Elab::Project(_, _) | Elab::Block(_) => false,
        }
    }

    pub fn is_polymorphic(&self) -> bool {
        match self {
            Elab::Pair(x, y) => x.is_polymorphic() || y.is_polymorphic(),
            Elab::Struct(_, v) => v.iter().any(|(_, x)| x.has_type()),
            Elab::Type | Elab::Unit | Elab::Builtin(_) | Elab::I32(_) | Elab::Var(_, _) => false,
            Elab::Binder(_, t) => t.has_type(),
            Elab::Fun(a, b, _) => a.is_polymorphic() || b.is_polymorphic(),
            Elab::App(_, _) | Elab::Project(_, _) | Elab::Block(_) => false,
        }
    }

    /// Is this a concrete type, i.e., we don't need to monomorphize it?
    pub fn is_concrete(&self) -> bool {
        match self {
            Elab::Var(_, _) => false,
            Elab::Pair(x, y) => x.is_concrete() && y.is_concrete(),
            Elab::Struct(_, v) => v.iter().all(|(_, x)| x.is_concrete()),
            Elab::Type
            | Elab::Unit
            | Elab::Builtin(_)
            // Not a type, but concrete, I guess? this should be unreachable
            | Elab::I32(_) => true,
            Elab::Binder(_, t) => t.is_concrete(),
            Elab::Fun(a, b, _) => a.is_concrete() && b.is_concrete(),
            // Both of these shouldn't happen unless the first param is neutral and thus not concrete
            Elab::App(_, _)
            | Elab::Project(_, _)
            | Elab::Block(_) => false,
        }
    }

    /// Convert a `Elab` representing a type to the `LowTy` that Elabs of that type are stored as
    /// Right now, panics on many Elabs
    pub fn as_low_ty(&self) -> LowTy {
        match self {
            Elab::Builtin(Builtin::Int) => LowTy::Int,
            Elab::Unit => LowTy::Void,
            Elab::Binder(_, t) => t.as_low_ty(),
            Elab::Fun(from, to, _) => {
                LowTy::Fun(Box::new(from.as_low_ty()), Box::new(to.as_low_ty()))
            }
            Elab::Pair(a, b) => LowTy::Struct(vec![a.as_low_ty(), b.as_low_ty()]),
            Elab::Struct(_, v) => {
                let mut v: Vec<_> = v.iter().collect();
                v.sort_by_key(|(x, _)| x.raw());
                LowTy::Struct(v.into_iter().map(|(_, v)| v.as_low_ty()).collect())
            }
            // Type erasure
            Elab::Type => LowTy::Void,
            _ => panic!("{:?} is not supported", self),
        }
    }
}

/// A module in LowIR
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowMod {
    pub name: String,
    pub funs: Vec<LowFun>,
}

/// Top-level definitions are represented as functions in LowIR
/// This cannot take arguments, refer to LowIR::Fun for one that can
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowFun {
    pub name: String,
    pub ret_ty: LowTy,
    pub body: LowIR,
}

/// An expression in LowIR
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowIR {
    Unit,
    IntConst(u64),
    IntOp {
        op: IntOp,
        lhs: Box<LowIR>,
        rhs: Box<LowIR>,
    },
    Let(Sym, Box<LowIR>, Box<LowIR>),
    Local(Sym),
    Global(String),
    Struct(Vec<LowIR>),
    Fun(Sym, LowTy, Box<LowIR>, LowTy),
    Call(Box<LowIR>, Box<LowIR>),
}

impl Elab {
    /// Convert to LowIR, within the Salsa framework. Returns `None` if it's polymorphic
    ///
    /// Most work should be done here and not in LowIR::codegen()
    pub fn as_low(&self, db: &impl MainGroup, env: &mut TempEnv) -> Option<LowIR> {
        Some(match self {
            // Type erasure
            _ if self.get_type(env) == Elab::Type => LowIR::Unit,
            Elab::Unit => LowIR::Unit,
            Elab::I32(i) => LowIR::IntConst(unsafe { std::mem::transmute::<i32, u32>(*i) } as u64),
            Elab::Var(x, ty) => {
                if ty.is_concrete() {
                    db.mangle(env.scope.clone(), *x).map(LowIR::Global).unwrap_or(LowIR::Local(*x))
                } else {
                    return None;
                }
            }
            Elab::Pair(a, b) => {
                let a = a.as_low(db, env)?;
                let b = b.as_low(db, env)?;
                LowIR::Struct(vec![a, b])
            }
            Elab::Struct(_, iv) => {
                let mut rv = Vec::new();
                for (name, val) in iv {
                    rv.push((name, val.as_low(db, env)?));
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowIR::Struct(rv.into_iter().map(|(_, v)| v).collect())
            }
            Elab::Block(v) => {
                let mut iter = v.iter().rev();
                let mut last = match iter.next().unwrap() {
                    ElabStmt::Def(_, _) => LowIR::Unit,
                    ElabStmt::Expr(e) => e.as_low(db, env)?,
                };
                for i in iter {
                    match i {
                        ElabStmt::Expr(_) => (),
                        ElabStmt::Def(name, val) => {
                            let val = val.as_low(db, env)?;
                            last = LowIR::Let(*name, Box::new(val), Box::new(last));
                        }
                    }
                }
                last
            }
            Elab::Fun(arg, body, ret_ty) => {
                if !ret_ty.is_concrete() || !arg.is_concrete() {
                    // Don't lower this function yet, wait until it's called
                    return None;
                }
                match &**arg {
                    Elab::Binder(arg, ty) => {
                        let body = body.as_low(db, env)?;
                        LowIR::Fun(*arg, ty.as_low_ty(), Box::new(body), ret_ty.as_low_ty())
                    }
                    _ => panic!("no pattern matching allowed yet"),
                }
            }
            Elab::App(f, x) => {
                if let Elab::Fun(from, _, _) = &f.get_type(env) {
                    if from.is_polymorphic() {
                        // Inline it
                        let mut s = self.cloned(&mut env.clone());
                        s.update_db(db, env.scope());
                        // Only recurse if it actually did something
                        if s.whnf(env) {
                            return s.as_low(db, env);
                        }
                    }
                } else {
                    panic!("not function type")
                }
                let f = f.as_low(db, env)?;
                let x = x.as_low(db, env)?;
                LowIR::Call(Box::new(f), Box::new(x))
            }
            _ => panic!("{:?} not supported (ir)", self),
        })
    }
}

impl LowIR {
    /// Convert this expression into an LLVM Elab
    ///
    /// Should be really simple, complex things belong in STerm::as_low
    fn codegen<'ctx>(
        &self,
        ctx: &mut CodegenCtx<'ctx>,
        module: &Module<'ctx>,
    ) -> AnyValueEnum<'ctx> {
        match self {
            LowIR::Unit => ctx.context.bool_type().const_int(0, false).into(),
            LowIR::IntConst(i) => ctx.context.i32_type().const_int(*i, false).into(),
            LowIR::IntOp { op, lhs, rhs } => {
                let lhs = lhs.codegen(ctx, module).into_int_value();
                let rhs = rhs.codegen(ctx, module).into_int_value();
                match op {
                    IntOp::Add => ctx.builder.build_int_add(lhs, rhs, "add"),
                    IntOp::Sub => ctx.builder.build_int_sub(lhs, rhs, "sub"),
                }
                .into()
            }
            LowIR::Struct(v) => {
                let values: Vec<BasicValueEnum> = v
                    .iter()
                    .map(|x| x.codegen(ctx, module).try_into().unwrap())
                    .collect();
                let types: Vec<_> = values.iter().map(|x| x.get_type()).collect();
                ctx.context
                    .struct_type(&types, false)
                    .const_named_struct(&values)
                    .as_any_value_enum()
            }
            LowIR::Let(var, val, body) => {
                let val = val.codegen(ctx, module);
                ctx.locals.insert(*var, val);
                body.codegen(ctx, module)
            }
            LowIR::Local(var) => *ctx.locals.get(var).expect("Used nonexistent local"),
            LowIR::Global(name) => ctx
                .builder
                .build_call(module.get_function(name).unwrap(), &[], name)
                .as_any_value_enum(),
            LowIR::Fun(arg, arg_ty, body, ret_ty) => {
                let bb = ctx.builder.get_insert_block().unwrap();
                let name = "$_anonymous_fun";

                let fun = module.add_function(
                    &name,
                    ret_ty.llvm_fn_type(&ctx.context, &[arg_ty.clone()]),
                    None,
                );
                let entry = ctx.context.append_basic_block(fun, "entry");
                ctx.builder.position_at_end(entry);
                ctx.locals
                    .insert(*arg, fun.get_first_param().unwrap().as_any_value_enum());

                let body: BasicValueEnum = body.codegen(ctx, module).try_into().unwrap();
                ctx.builder.build_return(Some(&body as &_));

                ctx.builder.position_at_end(bb);
                fun.as_any_value_enum()
            }
            LowIR::Call(f, x) => {
                let f = f.codegen(ctx, module).into_pointer_value();
                let x = x.codegen(ctx, module).try_into().unwrap();
                ctx.builder.build_call(f, &[x], "call").as_any_value_enum()
            }
        }
    }
}

/// An integer math operation. Currently not supported in the main language
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum IntOp {
    Add,
    Sub,
}

impl LowFun {
    /// Add the function definition represented by this `LowFun` to the passed LLVM `Module`
    fn codegen<'ctx>(&self, ctx: &mut CodegenCtx<'ctx>, module: &Module<'ctx>) {
        let fun = module.add_function(
            &self.name,
            self.ret_ty.llvm_fn_type(&ctx.context, &[]),
            None,
        );
        let entry = ctx.context.append_basic_block(fun, "entry");
        ctx.builder.position_at_end(entry);
        if self.ret_ty != LowTy::Void {
            let ret_val: BasicValueEnum = self.body.codegen(ctx, module).try_into().unwrap();
            ctx.builder.build_return(Some(&ret_val as &_));
        } else {
            ctx.builder.build_return(None);
        }
    }
}

impl LowMod {
    /// Convert this `LowMod` into an LLVM `Module`
    pub fn codegen<'ctx>(&self, ctx: &mut CodegenCtx<'ctx>) -> Module<'ctx> {
        let module = ctx.context.create_module(&self.name);
        for i in self.funs.iter() {
            i.codegen(ctx, &module);
        }
        module
    }
}
