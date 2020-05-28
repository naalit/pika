//! We use Inkwell to generate LLVM.
//! Unfortunately, Inkwell is impossible to integrate with Salsa, for two reasons:
//! - Everything uses lifetimes, and Salsa currently doesn't support those *at all*
//! - Most things aren't thread safe, which Salsa requires
//! So, in Salsa, we convert terms into LowIR, which is supposed to be very close to LLVM.
//! We convert that into LLVM outside of Salsa, and hopefully that requires hardly any work - most should be done in Salsa.

use crate::{
    common::*,
    eval::Value,
    term::{Builtin, Def, STerm, Statement, Term},
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
                x.llvm(ctx)
                    .try_into()
                    .expect("Parameter types must be basic!")
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
impl Value {
    /// Convert a `Value` representing a type to the `LowTy` that values of that type are stored as
    /// Right now, panics on many values
    pub fn as_low_ty(&self) -> LowTy {
        match self {
            Value::Builtin(Builtin::Int) => LowTy::Int,
            Value::Unit => LowTy::Void,
            Value::Binder(_, Some(t)) => t.as_low_ty(),
            Value::Fun(from, to) => {
                LowTy::Fun(Box::new(from.as_low_ty()), Box::new(to.as_low_ty()))
            }
            Value::Pair(a, b) => LowTy::Struct(vec![a.as_low_ty(), b.as_low_ty()]),
            Value::Struct(v) => {
                let mut v: Vec<_> = v.iter().collect();
                v.sort_by_key(|(x, _)| x.raw());
                LowTy::Struct(v.into_iter().map(|(_, v)| v.as_low_ty()).collect())
            }
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

impl STerm {
    /// Convert to LowIR, within the Salsa framework
    ///
    /// Most work should be done here and not in LowIR::codegen()
    pub fn as_low(&self, db: &impl MainGroup, env: &mut TempEnv) -> LowIR {
        match &**self {
            Term::Unit => LowIR::Unit,
            Term::I32(i) => LowIR::IntConst(unsafe { std::mem::transmute::<i32, u32>(*i) } as u64),
            Term::Var(x) => db
                .mangle(env.scope.clone(), *x)
                .map(LowIR::Global)
                .unwrap_or(LowIR::Local(*x)),
            Term::Pair(a, b) => {
                let a = a.as_low(db, env);
                let b = b.as_low(db, env);
                LowIR::Struct(vec![a, b])
            }
            Term::Struct(_, v) => {
                let mut v = v.clone();
                v.sort_by_key(|(x, _)| x.raw());
                LowIR::Struct(v.into_iter().map(|(_, v)| v.as_low(db, env)).collect())
            }
            Term::Block(v) => {
                let mut iter = v.iter().rev();
                let mut last = match iter.next().unwrap() {
                    Statement::Def(_) => LowIR::Unit,
                    Statement::Expr(e) => e.as_low(db, env),
                };
                for i in iter {
                    match i {
                        Statement::Expr(_) => (),
                        Statement::Def(Def(name, val)) => {
                            let val = val.as_low(db, env);
                            last = LowIR::Let(**name, Box::new(val), Box::new(last));
                        }
                    }
                }
                last
            }
            Term::Fun(arg, body) => {
                let ty = crate::bicheck::synth(self, db, env).unwrap();
                let (arg_ty, arg_real, ret_ty) = match ty {
                    Value::Fun(a, r) => (a.as_low_ty(), a.cloned(&mut env.clone()), r.as_low_ty()),
                    t => panic!("not a function type?: {}", WithContext(&env.bindings(), &t)),
                };
                match &**arg {
                    Term::Binder(arg, _) => {
                        env.set_ty(*arg, arg_real);
                        let body = body.as_low(db, env);
                        LowIR::Fun(*arg, arg_ty, Box::new(body), ret_ty)
                    }
                    _ => panic!("no pattern matching allowed yet"),
                }
            }
            Term::App(f, x) => {
                let f = f.as_low(db, env);
                let x = x.as_low(db, env);
                LowIR::Call(Box::new(f), Box::new(x))
            }
            _ => panic!("{:?} not supported (ir)", self),
        }
    }
}

impl LowIR {
    /// Convert this expression into an LLVM value
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
