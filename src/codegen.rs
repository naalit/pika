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
use std::convert::{TryFrom, TryInto};

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
    /// A 32-bit integers
    Int,
    /// A `void*` used for unknown closure environments. LLVM doesn't have `void*`, though, so it's really an `i8*`
    VoidPtr,
    /// Currently no functions are actually void, this is an alias for `i1`, where Pika's `()` compiles to `false`
    Void,
    /// A borrowed closure (the environment is essentially a `void*`), which you can call or pass as an argument
    ClosRef {
        from: Box<LowTy>,
        to: Box<LowTy>,
    },
    /// An owned closure (with a known environment), which is mostly used for returning from functions
    ClosOwn {
        from: Box<LowTy>,
        to: Box<LowTy>,
        upvalues: Vec<LowTy>,
    },
    /// No distinction between pairs and structs like in the main language
    /// Struct fields are stored in order of raw symbol numbers, which is NOT stable across modules or recompiles
    /// It is stable within one compilation of a module, though, which is enough for now
    Struct(Vec<LowTy>),
}
impl LowTy {
    /// Create an LLVM function type that returns `self`
    fn llvm_fn_type<'ctx>(&self, ctx: &'ctx Context, oparams: &[LowTy]) -> FunctionType<'ctx> {
        let params: Vec<_> = oparams
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
            LowTy::VoidPtr => ctx
                .i8_type()
                .ptr_type(inkwell::AddressSpace::Generic)
                .fn_type(&params, false),
            LowTy::Int => ctx.i32_type().fn_type(&params, false),
            LowTy::Void => ctx.bool_type().fn_type(&params, false),
            LowTy::ClosRef { from, to } => {
                let fun_ty = to.llvm_fn_type(ctx, &[LowTy::VoidPtr, (**from).clone()]);
                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                let clos_ty = ctx.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        LowTy::VoidPtr.llvm(ctx).try_into().unwrap(),
                    ],
                    false,
                );
                clos_ty.fn_type(&params, false)
            }
            LowTy::ClosOwn { from, to, upvalues } => {
                let env_struct_type = LowTy::Struct(upvalues.clone());
                let fun_ty = to.llvm_fn_type(ctx, &[LowTy::VoidPtr, (**from).clone()]);
                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                let clos_ty = ctx.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        env_struct_type.llvm(ctx).try_into().unwrap(),
                    ],
                    false,
                );
                clos_ty.fn_type(&params, false)
            }
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
            LowTy::VoidPtr => ctx
                .i8_type()
                .ptr_type(inkwell::AddressSpace::Generic)
                .as_any_type_enum(),
            LowTy::Int => AnyTypeEnum::IntType(ctx.i32_type()),
            LowTy::Void => ctx.bool_type().as_any_type_enum(),
            LowTy::ClosRef { from, to } => {
                println!("LLVM-izing borrowed closure type");
                // Just use a pointer, since we don't know what we're actually passing
                let fun_ty = to.llvm_fn_type(ctx, &[LowTy::VoidPtr, (**from).clone()]);
                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                ctx.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        LowTy::VoidPtr.llvm(ctx).try_into().unwrap(),
                    ],
                    false,
                )
                .as_any_type_enum()
            }
            LowTy::ClosOwn { from, to, upvalues } => {
                println!("LLVM-izing owned closure type");
                let env_struct_type = LowTy::Struct(upvalues.clone());
                let fun_ty = to.llvm_fn_type(ctx, &[LowTy::VoidPtr, (**from).clone()]);
                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                ctx.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        env_struct_type.llvm(ctx).try_into().unwrap(),
                    ],
                    false,
                )
                .as_any_type_enum()
            }
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
            Elab::Fun(from, to, _) => LowTy::ClosRef {
                from: Box::new(from.as_low_ty()),
                to: Box::new(to.as_low_ty()),
            },
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

impl Elab {
    /// Convert to LowIR, within the Salsa framework. Returns `None` if it's polymorphic
    ///
    /// Most work should be done here and not in LowIR::codegen()
    pub fn as_low<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Option<LowIR> {
        Some(match self {
            // Type erasure
            _ if self.get_type(env) == Elab::Type => LowIR::Unit,
            Elab::Unit => LowIR::Unit,
            Elab::I32(i) => LowIR::IntConst(unsafe { std::mem::transmute::<i32, u32>(*i) } as u64),
            Elab::Var(x, ty) => {
                if ty.is_concrete() {
                    env.db
                        .mangle(env.scope.clone(), *x)
                        .map(|s| LowIR::Global(*x, s))
                        .unwrap_or(LowIR::Local(*x))
                } else {
                    return None;
                }
            }
            Elab::Pair(a, b) => {
                let a = a.as_low(env)?;
                let b = b.as_low(env)?;
                LowIR::Struct(vec![a, b])
            }
            Elab::Struct(_, iv) => {
                let mut rv = Vec::new();
                for (name, val) in iv {
                    rv.push((name, val.as_low(env)?));
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowIR::Struct(rv.into_iter().map(|(_, v)| v).collect())
            }
            Elab::Block(v) => {
                let mut iter = v.iter().rev();
                let mut last = match iter.next().unwrap() {
                    ElabStmt::Def(_, _) => LowIR::Unit,
                    ElabStmt::Expr(e) => e.as_low(env)?,
                };
                for i in iter {
                    match i {
                        ElabStmt::Expr(_) => (),
                        ElabStmt::Def(name, val) => {
                            let val = val.as_low(env)?;
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
                let upvalues: Vec<_> = env
                    .tys
                    .iter()
                    .filter(|(s, _)| body.uses(**s))
                    .map(|(s, t)| (*s, t.as_low_ty()))
                    .collect();
                match &**arg {
                    Elab::Binder(arg, ty) => {
                        // We need to add it to the environment so we know it exists
                        env.set_ty(*arg, ty.cloned(&mut env.clone()));
                        let body = body.as_low(env)?;
                        let ret_ty = body.get_type(env);
                        println!("Ret_ty = {:?}", ret_ty);
                        LowIR::Closure {
                            arg_name: *arg,
                            arg_ty: ty.as_low_ty(),
                            ret_ty,
                            body: Box::new(body),
                            upvalues,
                        }
                    }
                    _ => panic!("no pattern matching allowed yet"),
                }
            }
            Elab::App(f, x) => {
                if let Elab::Fun(from, _, _) = &f.get_type(env) {
                    if from.is_polymorphic() {
                        // Inline it
                        let mut s = self.cloned(&mut env.clone());
                        // Only recurse if it actually did something
                        if s.whnf(env) {
                            return s.as_low(env);
                        }
                    }
                } else {
                    panic!("not function type")
                }
                // We borrow both the function and the argument
                let f = f.as_low(env)?.borrow(env);
                let x = x.as_low(env)?.borrow(env);
                LowIR::Call(Box::new(f), Box::new(x))
            }
            _ => panic!("{:?} not supported (ir)", self),
        })
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
    Global(Sym, String),
    Struct(Vec<LowIR>),
    /// Wraps an owned closure and turns it into a borrowed one (takes a pointer to the environment and bitcasts it to `void*`)
    ClosureBorrow(Box<LowIR>),
    /// An owned closure
    Closure {
        arg_name: Sym,
        arg_ty: LowTy,
        upvalues: Vec<(Sym, LowTy)>,
        ret_ty: LowTy,
        body: Box<LowIR>,
    },
    Call(Box<LowIR>, Box<LowIR>),
}

impl LowIR {
    pub fn borrow<T: MainGroup>(self, env: &TempEnv<T>) -> Self {
        if let LowTy::ClosOwn { .. } = self.get_type(env) {
            LowIR::ClosureBorrow(Box::new(self))
        } else {
            self
        }
    }

    pub fn get_type<T: MainGroup>(&self, env: &TempEnv<T>) -> LowTy {
        match self {
            LowIR::Unit => LowTy::Void,
            LowIR::IntConst(_) => LowTy::Int,
            LowIR::IntOp { .. } => LowTy::Int,
            LowIR::Struct(v) => LowTy::Struct(v.iter().map(|x| x.get_type(env)).collect()),
            LowIR::Let(_, _, body) => body.get_type(env),
            LowIR::Local(s) => env.ty(*s).unwrap().cloned(&mut env.clone()).as_low_ty(),
            LowIR::Global(s, _) => env.db.low_fun(env.scope(), *s).unwrap().ret_ty,
            LowIR::Call(f, _) => match f.get_type(env) {
                LowTy::ClosRef { to, .. } | LowTy::ClosOwn { to, .. } => *to,
                _ => panic!("not a function LowTy"),
            },
            LowIR::ClosureBorrow(c) => {
                if let LowTy::ClosOwn { to, from, .. } = c.get_type(env) {
                    LowTy::ClosRef { to, from }
                } else {
                    panic!("ClosureBorrow inner not an owned closure")
                }
            }
            LowIR::Closure {
                arg_ty,
                ret_ty,
                upvalues,
                ..
            } => LowTy::ClosOwn {
                from: Box::new(arg_ty.clone()),
                to: Box::new(ret_ty.clone()),
                upvalues: upvalues.iter().map(|(_, t)| t.clone()).collect(),
            },
        }
    }

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
                let mut struct_val = ctx
                    .context
                    .struct_type(&types, false)
                    .get_undef()
                    .as_aggregate_value_enum();
                for (i, v) in values.into_iter().enumerate() {
                    struct_val = ctx
                        .builder
                        .build_insert_value(struct_val, v, i as u32, "struct")
                        .unwrap();
                }
                struct_val.as_any_value_enum()
            }
            LowIR::Let(var, val, body) => {
                let val = val.codegen(ctx, module);
                ctx.locals.insert(*var, val);
                body.codegen(ctx, module)
            }
            LowIR::Local(var) => *ctx.locals.get(var).expect("Used nonexistent local"),
            LowIR::Global(_, name) => ctx
                .builder
                .build_call(module.get_function(name).unwrap(), &[], name)
                .as_any_value_enum(),
            LowIR::Closure {
                arg_name,
                arg_ty,
                body,
                ret_ty,
                upvalues,
            } => {
                let env_values: Vec<_> = upvalues
                    .iter()
                    .map(|(n, _)| {
                        BasicValueEnum::try_from(*ctx.locals.get(n).expect("Upvalue doesn't exist"))
                            .unwrap()
                    })
                    .collect();
                let env_types: Vec<_> = upvalues.iter().map(|(_, t)| t.clone()).collect();
                let env_struct_type = LowTy::Struct(env_types);
                let mut env_struct = env_struct_type.llvm(&ctx.context)
                    .into_struct_type()
                    .get_undef()
                    .as_aggregate_value_enum();
                for (i, v) in env_values.into_iter().enumerate() {
                    env_struct = ctx
                        .builder
                        .build_insert_value(env_struct, v, i as u32, "struct")
                        .unwrap();
                }

                let bb = ctx.builder.get_insert_block().unwrap();
                let name = "$_closure";

                let fun_ty = ret_ty.llvm_fn_type(&ctx.context, &[LowTy::VoidPtr, arg_ty.clone()]);
                let fun = module.add_function(&name, fun_ty, None);
                let entry = ctx.context.append_basic_block(fun, "entry");
                ctx.builder.position_at_end(entry);

                let mut old_locals = HashMap::new();
                std::mem::swap(&mut old_locals, &mut ctx.locals);
                ctx.locals
                    .insert(*arg_name, fun.get_last_param().unwrap().as_any_value_enum());
                // Add upvalues to local environment
                let local_env = fun.get_first_param().unwrap().into_pointer_value();
                let local_env = ctx
                    .builder
                    .build_bitcast(
                        local_env,
                        env_struct_type
                            .llvm(&ctx.context)
                            .into_struct_type()
                            .ptr_type(inkwell::AddressSpace::Generic),
                        name,
                    )
                    .into_pointer_value();
                let local_env = ctx
                    .builder
                    .build_load(local_env, "local_env")
                    .into_struct_value();
                for (i, (name, _)) in upvalues.iter().enumerate() {
                    let val = ctx
                        .builder
                        .build_extract_value(local_env, i as u32, "$_upvalue")
                        .unwrap();
                    ctx.locals.insert(*name, val.as_any_value_enum());
                }

                let body: BasicValueEnum = body.codegen(ctx, module).try_into().unwrap();
                ctx.builder.build_return(Some(&body as &_));

                // Go back to the original function
                std::mem::swap(&mut old_locals, &mut ctx.locals);
                ctx.builder.position_at_end(bb);

                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                let clos_ty = ctx.context.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        env_struct_type.llvm(&ctx.context).try_into().unwrap(),
                    ],
                    false,
                );
                // Not sure if this works
                let fun_ptr = fun.as_any_value_enum().into_pointer_value();
                let closure = clos_ty.get_undef();
                let closure = ctx
                    .builder
                    .build_insert_value(closure, fun_ptr, 0, "clos.partial")
                    .unwrap();
                let closure = ctx
                    .builder
                    .build_insert_value(closure, env_struct, 1, "clos")
                    .unwrap();
                closure.as_any_value_enum()
            }
            LowIR::ClosureBorrow(f) => {
                // Extract the function pointer and environment from the closure
                let f_struct = f.codegen(ctx, module).into_struct_value();
                let f_ptr = ctx
                    .builder
                    .build_extract_value(f_struct, 0, "fun")
                    .unwrap()
                    .into_pointer_value();
                let f_rest = ctx.builder.build_extract_value(f_struct, 1, "env").unwrap();
                let rest_ptr = ctx.builder.build_alloca(f_rest.get_type(), "env_ptr");
                ctx.builder.build_store(rest_ptr, f_rest);
                let void_ptr_ty =
                    BasicTypeEnum::try_from(LowTy::VoidPtr.llvm(&ctx.context)).unwrap();
                let rest_ptr = ctx.builder.build_bitcast(rest_ptr, void_ptr_ty, "env_cast");

                // Create a new struct
                let ref_type = ctx
                    .context
                    .struct_type(&[f_ptr.get_type().as_basic_type_enum(), void_ptr_ty], false);
                let closure_ref = ref_type.get_undef();
                let closure_ref = ctx
                    .builder
                    .build_insert_value(closure_ref, f_ptr, 0, "clos_ref.partial")
                    .unwrap();
                let closure_ref = ctx
                    .builder
                    .build_insert_value(closure_ref, rest_ptr, 1, "clos_ref")
                    .unwrap();
                closure_ref.as_any_value_enum()
            }
            LowIR::Call(f, x) => {
                let x = x.codegen(ctx, module).try_into().unwrap();

                // Extract the function pointer and environment from the closure
                // We're calling a borrowed closure, so it has a pointer to the environment already
                let f_struct = f.codegen(ctx, module).into_struct_value();
                let f_ptr = ctx
                    .builder
                    .build_extract_value(f_struct, 0, "fun")
                    .unwrap()
                    .into_pointer_value();
                let f_rest = ctx.builder.build_extract_value(f_struct, 1, "env").unwrap();

                ctx.builder
                    .build_call(f_ptr, &[f_rest, x], "call")
                    .as_any_value_enum()
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
