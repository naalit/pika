//! We use Inkwell to generate LLVM.
//! Unfortunately, Inkwell is impossible to integrate with Salsa, for two reasons:
//! - Everything uses lifetimes, and Salsa currently doesn't support those *at all*
//! - Most things aren't thread safe, which Salsa requires
//!
//! So, in Salsa, we convert terms into LowIR, which is supposed to be very close to LLVM.
//! We convert that into LLVM outside of Salsa, and hopefully that requires hardly any work - most should be done in Salsa.

use crate::{common::*, low::*};
use inkwell::context::Context;
use inkwell::{basic_block::BasicBlock, builder::Builder, module::Module, types::*, values::*};
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};

/// We need one of these to generate any LLVM code, but not to generate LowIR
pub struct CodegenCtx<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    locals: HashMap<Sym, AnyValueEnum<'ctx>>,
    blocks: HashMap<BlockId, BasicBlock<'ctx>>,
    branches: Vec<(BlockId, BlockId, BasicBlock<'ctx>)>,
    current_block: BlockId,
}
impl<'ctx> CodegenCtx<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        CodegenCtx {
            context,
            builder: context.create_builder(),
            locals: HashMap::new(),
            blocks: HashMap::new(),
            branches: Vec::new(),
            current_block: next_block(),
        }
    }
}

impl FunAttr {
    fn llvm_enum(self) -> u32 {
        let name = match self {
            FunAttr::AlwaysInline => "alwaysinline",
        };
        inkwell::attributes::Attribute::get_named_enum_kind_id(name)
    }
}

/// Get the smallest IntType that can differentiate between all the things in `v`
/// One of `i1, i8, i16, i32, i64`
fn tag_type<'ctx, T>(v: &[T], ctx: &'ctx Context) -> IntType<'ctx> {
    ctx.custom_width_int_type(tag_width(v))
}

impl LowTy {
    /// The size of this type in bytes, on a 64-bit platform
    /// It doesn't need to be perfect, it's just used for finding the biggest type in a union
    fn size<'ctx>(&self, ctx: &'ctx Context) -> u64 {
        if let Some(size) = self
            .llvm(ctx)
            .size_of()
            .and_then(|x| x.get_zero_extended_constant())
        {
            return size;
        }
        let size = match self {
            LowTy::Bool => 1,
            LowTy::Int(bits) => (*bits as u64) / 8,
            LowTy::VoidPtr => 8,
            LowTy::Unit => 0,
            LowTy::ClosRef { .. } => 16, // 8 for the fun ptr, 8 for the env ptr
            // Guessing at padding
            LowTy::ClosOwn { upvalues, .. } => {
                8 + upvalues
                    .iter()
                    .map(|x| {
                        let s = x.size(ctx);
                        if s == 0 {
                            0
                        } else {
                            s.max(8)
                        }
                    })
                    .sum::<u64>()
            }
            LowTy::Struct(v) => v.iter().map(|x| x.size(ctx).max(8)).sum(),
            // The tag is 8 bytes, because it would be anyway with padding
            LowTy::Union(v) => 8 + v.iter().map(|x| x.size(ctx)).max().unwrap(),
            LowTy::Never => panic!("never type has no size"),
        };
        #[cfg(feature = "logging")]
        eprintln!("compiler warning: LLVM doesn't have a constant size for {:?}, guessing at size {} bytes", self, size);
        size
    }

    /// Create an LLVM function type that returns `self`
    fn llvm_fn_type<'ctx>(&self, ctx: &'ctx Context, oparams: &[LowTy]) -> FunctionType<'ctx> {
        let params: Vec<_> = oparams.iter().map(|x| x.llvm(ctx)).collect();
        let ret_ty = self.llvm(ctx);
        match ret_ty {
            BasicTypeEnum::ArrayType(t) => t.fn_type(&params, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&params, false),
            BasicTypeEnum::IntType(t) => t.fn_type(&params, false),
            BasicTypeEnum::PointerType(t) => t.fn_type(&params, false),
            BasicTypeEnum::StructType(t) => t.fn_type(&params, false),
            BasicTypeEnum::VectorType(t) => t.fn_type(&params, false),
        }
    }

    /// Get the LLVM representation of `self`
    fn llvm<'ctx>(&self, ctx: &'ctx Context) -> BasicTypeEnum<'ctx> {
        match self {
            LowTy::Bool => ctx.bool_type().as_basic_type_enum(),
            LowTy::VoidPtr => ctx
                .i8_type()
                .ptr_type(inkwell::AddressSpace::Generic)
                .as_basic_type_enum(),
            LowTy::Int(i) => ctx.custom_width_int_type(*i).as_basic_type_enum(),
            LowTy::Unit => ctx.struct_type(&[], false).as_basic_type_enum(),
            LowTy::ClosRef { from, to } => {
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
                .as_basic_type_enum()
            }
            LowTy::ClosOwn { from, to, upvalues } => {
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
                .as_basic_type_enum()
            }
            LowTy::Struct(v) => ctx
                .struct_type(
                    &v.iter()
                        .map(|a| a.llvm(ctx).try_into().unwrap())
                        .collect::<Vec<_>>(),
                    false,
                )
                .as_basic_type_enum(),
            LowTy::Union(v) => {
                if v.len() == 1 {
                    return v[0].llvm(ctx);
                }
                let payload_type = v.iter().max_by_key(|x| x.size(ctx)).unwrap().llvm(ctx);
                let tag_type = tag_type(&v, ctx).as_basic_type_enum();
                ctx.struct_type(&[tag_type, payload_type], false)
                    .as_basic_type_enum()
            }
            LowTy::Never => panic!("never type has no llvm type"),
        }
    }
}

/// Gets the `undef` value of a given type
fn undef_of(x: BasicTypeEnum) -> BasicValueEnum {
    match x {
        BasicTypeEnum::ArrayType(x) => x.get_undef().into(),
        BasicTypeEnum::FloatType(x) => x.get_undef().into(),
        BasicTypeEnum::IntType(x) => x.get_undef().into(),
        BasicTypeEnum::PointerType(x) => x.get_undef().into(),
        BasicTypeEnum::StructType(x) => x.get_undef().into(),
        BasicTypeEnum::VectorType(x) => x.get_undef().into(),
    }
}

impl LowIR {
    /// Convert this expression into an LLVM value
    ///
    /// Should be fairly simple, complex things belong in STerm::as_low
    fn codegen<'ctx>(
        &self,
        ctx: &mut CodegenCtx<'ctx>,
        module: &Module<'ctx>,
    ) -> AnyValueEnum<'ctx> {
        match self {
            LowIR::Unit => ctx
                .context
                .struct_type(&[], false)
                .const_named_struct(&[])
                .into(),
            LowIR::IntConst(i) => ctx.context.i32_type().const_int(*i, false).into(),
            LowIR::SizedIntConst(n, i) => ctx
                .context
                .custom_width_int_type(*n)
                .const_int(*i, false)
                .into(),
            LowIR::IntOp { op, lhs, rhs } => {
                let lhs = lhs.codegen(ctx, module).into_int_value();
                let rhs = rhs.codegen(ctx, module).into_int_value();
                match op {
                    IntOp::Add => ctx.builder.build_int_add(lhs, rhs, "add"),
                    IntOp::Sub => ctx.builder.build_int_sub(lhs, rhs, "sub"),
                    IntOp::Mul => ctx.builder.build_int_mul(lhs, rhs, "mul"),
                    IntOp::Div => ctx.builder.build_int_signed_div(lhs, rhs, "div"),
                }
                .into()
            }
            LowIR::CompOp { op, lhs, rhs } => {
                let lhs = lhs.codegen(ctx, module).into_int_value();
                let rhs = rhs.codegen(ctx, module).into_int_value();
                match op {
                    CompOp::Eq => {
                        ctx.builder
                            .build_int_compare(inkwell::IntPredicate::EQ, lhs, rhs, "eq")
                    }
                }
                .into()
            }
            LowIR::BoolConst(b) => ctx.context.bool_type().const_int(*b as u64, false).into(),
            LowIR::BoolOp { op, lhs, rhs } => {
                let lhs = lhs.codegen(ctx, module).into_int_value();
                let rhs = rhs.codegen(ctx, module).into_int_value();
                match op {
                    BoolOp::And => ctx.builder.build_and(lhs, rhs, "and"),
                    BoolOp::Or => ctx.builder.build_or(lhs, rhs, "or"),
                }
                .into()
            }
            LowIR::Struct(v) => {
                let values: Vec<BasicValueEnum> = v
                    .iter()
                    .map(|(n, x)| {
                        let v = x.codegen(ctx, module);
                        ctx.locals.insert(*n, v);
                        v.try_into().unwrap()
                    })
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
            LowIR::Project(r, m) => {
                let r = r.codegen(ctx, module).into_struct_value();
                ctx.builder
                    .build_extract_value(r, *m as u32, "project")
                    .unwrap()
                    .as_any_value_enum()
            }
            LowIR::Let(var, val, body) => {
                let val = val.codegen(ctx, module);
                ctx.locals.insert(*var, val);
                body.codegen(ctx, module)
            }
            LowIR::Local(var) => *ctx.locals.get(var).expect("Used nonexistent local"),
            LowIR::Global(_, _, name) => ctx
                .builder
                .build_call(
                    module
                        .get_function(name)
                        .unwrap_or_else(|| panic!("No {}", name)),
                    &[],
                    name,
                )
                .as_any_value_enum(),
            LowIR::TypedGlobal(ty, name) => {
                let ty = LowTy::Struct(vec![ty.clone(), LowTy::Unit])
                    .llvm(&ctx.context)
                    .into_struct_type();

                let fun = module.get_function(name).unwrap();
                let fun_ptr = fun.as_any_value_enum().into_pointer_value();

                ctx.builder
                    .build_insert_value(ty.get_undef(), fun_ptr, 0, "clos")
                    .unwrap()
                    .as_any_value_enum()
            }
            LowIR::Closure {
                fun_name,
                attrs,
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
                let mut env_struct = env_struct_type
                    .llvm(&ctx.context)
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

                let fun_ty = ret_ty.llvm_fn_type(&ctx.context, &[LowTy::VoidPtr, arg_ty.clone()]);
                let fun = module.add_function(&fun_name, fun_ty, None);
                for attr in attrs {
                    let attr = attr.llvm_enum();
                    let attr = ctx.context.create_enum_attribute(attr, 0);
                    fun.add_attribute(inkwell::attributes::AttributeLoc::Function, attr);
                }
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
                        "env",
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

                let body: BasicValueEnum = body
                    .codegen(ctx, module)
                    .try_into()
                    .unwrap_or_else(|_| panic!("{:?}", body));
                ctx.builder.build_return(Some(&body as &_));

                // Go back to the original function
                std::mem::swap(&mut old_locals, &mut ctx.locals);
                ctx.builder.position_at_end(bb);

                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                let clos_ty = ctx.context.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        env_struct_type.llvm(&ctx.context),
                    ],
                    false,
                );
                // Magic, might break eventually
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
            LowIR::Variant(tag, ty, val) => {
                let v = if let LowTy::Union(v) = ty {
                    v
                } else {
                    unreachable!()
                };

                if v.len() <= 1 {
                    return val.codegen(ctx, module);
                }

                let ty = ty.llvm(&ctx.context).into_struct_type();
                let payload_type = ty.get_field_type_at_index(1).unwrap();

                let tag = tag_type(v, &ctx.context).const_int(*tag, false);
                let val: BasicValueEnum = val.codegen(ctx, module).try_into().unwrap();
                let val_ty = val.get_type();
                let val_ptr = ctx.builder.build_alloca(val_ty, "payload_ptr");
                ctx.builder.build_store(val_ptr, val);
                let val_ptr = ctx
                    .builder
                    .build_bitcast(
                        val_ptr,
                        payload_type.ptr_type(inkwell::AddressSpace::Generic),
                        "payload_ptr_cast",
                    )
                    .into_pointer_value();
                // This reads some unititialized memory, but it's on the stack so it's not going to segfault, and it never uses the value so it's fine
                let val = ctx.builder.build_load(val_ptr, "payload");

                let ret = ty.get_undef();
                let ret = ctx
                    .builder
                    .build_insert_value(ret, tag, 0, "with_tag")
                    .unwrap();
                let ret = ctx
                    .builder
                    .build_insert_value(ret, val, 1, "with_val")
                    .unwrap();
                ret.as_any_value_enum()
            }
            LowIR::Switch(tag, cases) => {
                let tag = tag.codegen(ctx, module).into_int_value();
                let tag_ty = tag.get_type();

                let cur_block = ctx.builder.get_insert_block().unwrap();
                let blocks: Vec<(IntValue, BasicBlock)> = cases
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        (
                            tag_ty.const_int(i as u64, false),
                            ctx.context
                                .insert_basic_block_after(cur_block, &format!("case.{}", i)),
                        )
                    })
                    .collect();
                let else_block = ctx.context.insert_basic_block_after(
                    blocks.first().map(|(_, x)| *x).unwrap_or(cur_block),
                    "_catchall",
                );
                let _switch = ctx.builder.build_switch(tag, else_block, &blocks);

                // Mark the else block as unreachable
                ctx.builder.position_at_end(else_block);
                ctx.builder.build_unreachable();

                let after_block = ctx.context.insert_basic_block_after(else_block, "merge");

                // Only execute the branch code in its branch, then use a phi to merge them back together
                let mut ty = ctx.context.i32_type().as_basic_type_enum();
                let mut phis: Vec<(BasicValueEnum, BasicBlock)> = Vec::new();
                for ((_, block), val) in blocks.into_iter().zip(cases) {
                    ctx.builder.position_at_end(block);
                    let val = val.codegen(ctx, module);
                    ty = val.get_type().try_into().unwrap();
                    phis.push((BasicValueEnum::try_from(val).unwrap(), block));
                    ctx.builder.build_unconditional_branch(after_block);
                }

                ctx.builder.position_at_end(after_block);
                let phi = ctx.builder.build_phi(ty, "phi");
                let phis_dyn: Vec<(&dyn BasicValue, BasicBlock)> =
                    phis.iter().map(|(x, y)| (x as &_, *y)).collect();
                phi.add_incoming(&phis_dyn);

                phi.as_any_value_enum()
            }
            LowIR::Unreachable => {
                let inst = ctx.builder.build_unreachable().into();
                let cur_block = ctx.builder.get_insert_block().unwrap();
                let other_block = ctx
                    .context
                    .insert_basic_block_after(cur_block, "_unreachable");
                ctx.builder.position_at_end(other_block);
                inst
            }
            LowIR::Branch(b) => {
                ctx.branches.push((
                    ctx.current_block,
                    *b,
                    ctx.builder.get_insert_block().unwrap(),
                ));
                let v = ctx
                    .builder
                    .build_unconditional_branch(*ctx.blocks.get(b).unwrap())
                    .into();
                let u = ctx.context.insert_basic_block_after(
                    ctx.builder.get_insert_block().unwrap(),
                    "_unreachable_br",
                );
                ctx.builder.position_at_end(u);
                v
            }
            LowIR::If { cond, yes, no } => {
                let cond = cond.codegen(ctx, module).into_int_value();

                let cur_block = ctx.builder.get_insert_block().unwrap();

                let yes_block = ctx.context.insert_basic_block_after(cur_block, "true");
                let no_block = ctx.context.insert_basic_block_after(yes_block, "false");

                let if_ = ctx
                    .builder
                    .build_conditional_branch(cond, yes_block, no_block);

                let merge_block = ctx.context.insert_basic_block_after(no_block, "merge");

                ctx.builder.position_at_end(yes_block);
                let yes = yes.codegen(ctx, module);
                // Codegen'ing `yes` could have changed the block we're in
                let yes_block = ctx.builder.get_insert_block().unwrap();
                let ty = yes.get_type();
                ctx.builder.build_unconditional_branch(merge_block);

                ctx.builder.position_at_end(no_block);
                let no = no.codegen(ctx, module);
                let no_block = ctx.builder.get_insert_block().unwrap();
                ctx.builder.build_unconditional_branch(merge_block);

                ctx.builder.position_at_end(merge_block);
                let yes = BasicValueEnum::try_from(yes);
                let no = BasicValueEnum::try_from(no);

                if yes.is_ok() || no.is_ok() {
                    let yes = if let Ok(yes) = yes {
                        yes
                    } else {
                        undef_of(no.unwrap().get_type())
                    };
                    let no = if let Ok(no) = no {
                        no
                    } else {
                        undef_of(yes.get_type())
                    };

                    let phi = ctx
                        .builder
                        .build_phi::<BasicTypeEnum>(ty.try_into().unwrap(), "phi");
                    phi.add_incoming(&[(&yes as &_, yes_block), (&no as &_, no_block)]);

                    phi.as_any_value_enum()
                } else {
                    // If they're not BasicValues, they don't return anything, so we just stick something in here
                    if_.as_any_value_enum()
                }
            }
            LowIR::MultiSwitch {
                switch_on,
                cases,
                blocks,
            } => {
                let tag = switch_on.codegen(ctx, module).into_int_value();
                let tag_ty = tag.get_type();

                let cur_block = ctx.builder.get_insert_block().unwrap();
                let case_blocks: Vec<(IntValue, BasicBlock)> = cases
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        (
                            tag_ty.const_int(i as u64, false),
                            ctx.context
                                .insert_basic_block_after(cur_block, &format!("case.{}", i)),
                        )
                    })
                    .collect();
                let else_block = ctx.context.insert_basic_block_after(
                    case_blocks.first().map(|(_, x)| *x).unwrap_or(cur_block),
                    "_catchall",
                );
                let _switch = ctx.builder.build_switch(tag, else_block, &case_blocks);

                let bblocks: Vec<BasicBlock> = blocks
                    .iter()
                    .map(|_| {
                        ctx.context
                            .insert_basic_block_after(else_block, "_multi_block")
                    })
                    .collect();
                for (bb, (_, id, _)) in bblocks.iter().zip(blocks.iter()) {
                    ctx.blocks.insert(*id, *bb);
                }

                // Mark the else block as unreachable
                ctx.builder.position_at_end(else_block);
                ctx.builder.build_unreachable();

                for ((_, case_block), (id, val)) in case_blocks.into_iter().zip(cases) {
                    ctx.current_block = *id;
                    ctx.builder.position_at_end(case_block);
                    let _ = val.codegen(ctx, module);
                    // We're still in a basic block, but we shouldn't get here
                    ctx.builder.build_unreachable();
                }

                let after_block = ctx
                    .context
                    .insert_basic_block_after(bblocks[0], "_multi_switch_merge");

                // We use another phi for the return value of the target blocks
                let mut ret_phis: Vec<(BasicValueEnum, BasicBlock)> = Vec::new();
                let mut ty = ctx.context.i32_type().as_basic_type_enum();
                for ((phis, id, val), bblock) in blocks.iter().zip(bblocks) {
                    ctx.current_block = *id;
                    ctx.builder.position_at_end(bblock);

                    for Phi { incoming, result } in phis {
                        let ty: BasicTypeEnum = ctx
                            .locals
                            .get(&incoming.first().unwrap().1)
                            .unwrap()
                            .get_type()
                            .try_into()
                            .unwrap();
                        let phi = ctx.builder.build_phi(ty, "phi");
                        let incoming: Vec<(BasicValueEnum, BasicBlock)> = incoming
                            .iter()
                            .map(|(from_id, s)| {
                                let block = ctx
                                    .branches
                                    .iter()
                                    .find(|(from, to, _)| from == from_id && to == id)
                                    .unwrap()
                                    .2;
                                (
                                    BasicValueEnum::try_from(*ctx.locals.get(s).unwrap()).unwrap(),
                                    block,
                                )
                            })
                            .collect();
                        let phis_dyn: Vec<(&dyn BasicValue, BasicBlock)> =
                            incoming.iter().map(|(x, y)| (x as &_, *y)).collect();
                        phi.add_incoming(&phis_dyn);
                        ctx.locals.insert(*result, phi.as_any_value_enum());
                    }

                    let val = val.codegen(ctx, module);
                    ty = val.get_type().try_into().unwrap();
                    ret_phis.push((val.try_into().unwrap(), bblock));

                    ctx.builder.build_unconditional_branch(after_block);
                }

                ctx.builder.position_at_end(after_block);
                let phi = ctx.builder.build_phi(ty, "phi");
                let phis_dyn: Vec<(&dyn BasicValue, BasicBlock)> =
                    ret_phis.iter().map(|(x, y)| (x as &_, *y)).collect();
                phi.add_incoming(&phis_dyn);

                phi.as_any_value_enum()
            }
        }
    }
}

impl LowFun {
    /// Add the function declaration represented by this `LowFun` to the passed LLVM `Module`
    fn declare<'ctx>(&self, ctx: &CodegenCtx<'ctx>, module: &Module<'ctx>) -> FunctionValue<'ctx> {
        module.add_function(
            &self.name,
            self.ret_ty.llvm_fn_type(&ctx.context, &[]),
            None,
        )
    }

    /// Actually put the code in this `LowFun` into `fun`
    fn codegen<'ctx>(
        &self,
        ctx: &mut CodegenCtx<'ctx>,
        fun: FunctionValue<'ctx>,
        module: &Module<'ctx>,
    ) {
        let entry = ctx.context.append_basic_block(fun, "entry");
        ctx.builder.position_at_end(entry);
        let ret_val: BasicValueEnum = self.body.codegen(ctx, module).try_into().unwrap();
        ctx.builder.build_return(Some(&ret_val as &_));
    }
}

impl LowMod {
    /// Convert this `LowMod` into an LLVM `Module`
    pub fn codegen<'ctx>(&self, ctx: &mut CodegenCtx<'ctx>) -> Module<'ctx> {
        let module = ctx.context.create_module(&self.name);
        // Add all the declarations first so recursive and unordered functions work
        let funs: Vec<_> = self.funs.iter().map(|x| x.declare(ctx, &module)).collect();
        for (i, fun) in self.funs.iter().zip(funs) {
            i.codegen(ctx, fun, &module);
        }
        module
    }
}
