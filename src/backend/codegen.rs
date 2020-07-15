//! The LLVM interface lives here, since its thread-locality and `inkwell`'s lifetimes don't really work with Salsa.
use super::low::*;
use inkwell::{
    attributes::{Attribute, AttributeLoc},
    basic_block::BasicBlock,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    types::*,
    values::*,
    AddressSpace, IntPredicate,
};
use std::{
    collections::{HashMap, HashSet},
    convert::{TryFrom, TryInto},
    fmt::Debug,
};

// Some calling conventions
pub const TAILCC: u32 = 18;
pub const CCC: u32 = 0;
pub const FASTCC: u32 = 8;

/// We need one of these to generate any LLVM code, but not to generate LowIR
pub struct CodegenCtx<'ctx> {
    pub context: &'ctx Context,
    pub builder: Builder<'ctx>,
    pub locals: HashMap<Val, BasicValueEnum<'ctx>>,
    pub module: Module<'ctx>,
    pub halt: FunctionValue<'ctx>,
    pub stack_base: PointerValue<'ctx>,
    /// The current stack pointer. We thread this through function calls as needed.
    pub stack_ptr: PointerValue<'ctx>,
}
impl<'ctx> CodegenCtx<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        let module = context.create_module("main");

        // declare void @_pika_print_int(i32)
        let halt = module.add_function(
            "_pika_print_int",
            context
                .void_type()
                .fn_type(&[context.i32_type().as_basic_type_enum()], false),
            None,
        );

        let stack = module.add_global(
            context.i8_type().ptr_type(AddressSpace::Generic),
            None,
            "_pika_stack",
        );
        stack.set_initializer(
            &context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .const_null(),
        );
        let stack = stack.as_pointer_value();

        CodegenCtx {
            context,
            builder: context.create_builder(),
            locals: HashMap::new(),
            module,
            halt,
            stack_base: stack,
            stack_ptr: stack,
        }
    }

    /// Returns the i8* type, which we use as void* for e.g. closure environments
    pub fn voidptr(&self) -> BasicTypeEnum<'ctx> {
        self.context
            .i8_type()
            .ptr_type(AddressSpace::Generic)
            .as_basic_type_enum()
    }

    /// Allocate `size` bytes on the Pika stack
    pub fn alloca(&mut self, size: IntValue<'ctx>) -> PointerValue<'ctx> {
        // TODO bump down
        // TODO alignment
        // TODO segmented stack

        // To check if bugs are caused by stack handling, uncomment the two lines below to disable stack popping

        // self.stack_ptr = self.builder.build_load(self.stack_base, "_stack_ptr").into_pointer_value();
        let new_ptr = unsafe {
            self.builder
                .build_gep(self.stack_ptr, &[size], "_stack_push")
        };
        // self.builder.build_store(self.stack_base, new_ptr);
        let old = self.stack_ptr;
        self.stack_ptr = new_ptr;
        old
    }

    /// Allocate the Pika stack
    pub fn allocate_stack(&mut self) {
        let malloc = self.module.add_function(
            "malloc",
            self.context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .fn_type(&[self.context.i64_type().as_basic_type_enum()], false),
            None,
        );
        // Right now it's just 2KB, and not segmented
        let ptr = self
            .builder
            .build_call(
                malloc,
                &[self
                    .context
                    .i64_type()
                    .const_int(2048, false)
                    .as_basic_value_enum()],
                "_stack_ptr",
            )
            .try_as_basic_value()
            .left()
            .unwrap();
        self.builder.build_store(self.stack_base, ptr);
        self.stack_ptr = ptr.into_pointer_value();
    }
}

fn fn_type<'a>(params: &[BasicTypeEnum<'a>], x: BasicTypeEnum<'a>) -> FunctionType<'a> {
    match x {
        BasicTypeEnum::ArrayType(t) => t.fn_type(params, false),
        BasicTypeEnum::FloatType(t) => t.fn_type(params, false),
        BasicTypeEnum::IntType(t) => t.fn_type(params, false),
        BasicTypeEnum::PointerType(t) => t.fn_type(params, false),
        BasicTypeEnum::StructType(t) => t.fn_type(params, false),
        BasicTypeEnum::VectorType(t) => t.fn_type(params, false),
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

impl<'a> CodegenCtx<'a> {
    fn if_else<R: BasicValue<'a> + TryFrom<BasicValueEnum<'a>, Error = impl Debug>>(
        &self,
        cond: impl BasicValue<'a>,
        yes: impl FnOnce(&CodegenCtx<'a>) -> R,
        no: impl FnOnce(&CodegenCtx<'a>) -> R,
    ) -> R {
        let old_block = self.builder.get_insert_block().unwrap();

        let after_block = self.context.insert_basic_block_after(old_block, "merge");

        let yes_block = self
            .context
            .insert_basic_block_after(old_block, "yes_block");
        self.builder.position_at_end(yes_block);
        let yes_val = yes(self);
        let phi_type = yes_val.as_basic_value_enum().get_type();
        // They could have branched around in `yes()`, so we need to phi from *this* block
        let yes_block_f = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(after_block);

        let no_block = self.context.insert_basic_block_after(old_block, "no_block");
        self.builder.position_at_end(no_block);
        let no_val = no(self);
        // Same with `no()`
        let no_block_f = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(after_block);

        self.builder.position_at_end(old_block);
        self.builder.build_conditional_branch(
            cond.as_basic_value_enum().into_int_value(),
            yes_block,
            no_block,
        );

        self.builder.position_at_end(after_block);
        let phi = self.builder.build_phi(phi_type, "phi");
        phi.add_incoming(&[(&yes_val, yes_block_f), (&no_val, no_block_f)]);

        phi.as_basic_value().try_into().unwrap()
    }

    /// Like if_else(), but lets you mutate the context and phis back the stack pointer
    fn if_else_mut<R: BasicValue<'a> + TryFrom<BasicValueEnum<'a>, Error = impl Debug>>(
        &mut self,
        cond: impl BasicValue<'a>,
        yes: impl FnOnce(&mut CodegenCtx<'a>) -> R,
        no: impl FnOnce(&mut CodegenCtx<'a>) -> R,
    ) -> R {
        let old_block = self.builder.get_insert_block().unwrap();
        let old_stack_ptr = self.stack_ptr;

        let after_block = self.context.insert_basic_block_after(old_block, "merge");

        let yes_block = self
            .context
            .insert_basic_block_after(old_block, "yes_block");
        self.builder.position_at_end(yes_block);
        let yes_val = yes(self);
        let yes_stack_ptr = self.stack_ptr;
        let phi_type = yes_val.as_basic_value_enum().get_type();
        // They could have branched around in `yes()`, so we need to phi from *this* block
        let yes_block_f = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(after_block);

        self.stack_ptr = old_stack_ptr;
        let no_block = self.context.insert_basic_block_after(old_block, "no_block");
        self.builder.position_at_end(no_block);
        let no_val = no(self);
        let no_stack_ptr = self.stack_ptr;
        // Same with `no()`
        let no_block_f = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(after_block);

        self.builder.position_at_end(old_block);
        self.builder.build_conditional_branch(
            cond.as_basic_value_enum().into_int_value(),
            yes_block,
            no_block,
        );

        self.builder.position_at_end(after_block);
        let phi = self.builder.build_phi(phi_type, "phi");
        phi.add_incoming(&[(&yes_val, yes_block_f), (&no_val, no_block_f)]);
        let stack_ptr_phi = self.builder.build_phi(self.voidptr(), "stack_ptr_phi");
        stack_ptr_phi.add_incoming(&[(&yes_stack_ptr, yes_block_f), (&no_stack_ptr, no_block_f)]);
        self.stack_ptr = stack_ptr_phi.as_basic_value().into_pointer_value();

        phi.as_basic_value().try_into().unwrap()
    }
}

impl Ty {
    /// Either casts the `i8*` into the appropriate type, or loads it, depending on the size of the type.
    fn from_void_ptr<'a>(&self, ptr: PointerValue<'a>, ctx: &CodegenCtx<'a>) -> BasicValueEnum<'a> {
        match self {
            Ty::Int(size) => {
                // We do:
                // if size_of<iNN>() <= size_of<i8*>() {
                //   ptrtoint(ptr)
                // } else {
                //   load(ptr)
                // }
                // LLVM should optimize out the conditional easily.
                let int_type = ctx.context.custom_width_int_type(*size);
                let int_size = int_type.size_of();
                let ptr_size = ctx.voidptr().size_of().unwrap();
                ctx.if_else(
                    {
                        ctx.builder.build_int_compare(
                            IntPredicate::ULE,
                            int_size,
                            ptr_size,
                            "int_fits",
                        )
                    },
                    |ctx| {
                        ctx.builder
                            .build_ptr_to_int(ptr, int_type, "int_cast")
                            .as_basic_value_enum()
                    },
                    |ctx| {
                        // It needs to be word-aligned, but if `size` is a power of two, it must be either <= word_size or a multiple of the word size
                        assert!(
                            size.is_power_of_two(),
                            "Ty::Int may only be used with power-of-two bit widths, not {}",
                            size
                        );
                        let ptr_cast = ctx.builder.build_bitcast(
                            ptr,
                            int_type.ptr_type(AddressSpace::Generic),
                            "_ptr_cast",
                        );
                        ctx.builder
                            .build_load(ptr_cast.into_pointer_value(), "_load")
                    },
                )
            }
            Ty::Dyn(_) | Ty::Struct(_) | Ty::Fun | Ty::Cont => ptr.as_basic_value_enum(),
        }
    }

    /// Either casts into `i8*`, or allocates space on the stack and stores it there, depending on the size of the type.
    /// For types already stored somewhere, it just returns the same pointer unmodified.
    fn to_void_ptr<'a>(
        &self,
        val: BasicValueEnum<'a>,
        ctx: &mut CodegenCtx<'a>,
    ) -> PointerValue<'a> {
        match self {
            Ty::Int(size) => {
                // We do:
                // if size_of<iNN>() <= size_of<i8*>() {
                //   inttoptr(ptr)
                // } else {
                //   store(ptr)
                // }
                // LLVM should optimize out the conditional easily.
                let int_type = ctx.context.custom_width_int_type(*size);
                let int_size = int_type.size_of();
                let ptr_size = ctx.voidptr().size_of().unwrap();
                ctx.if_else_mut(
                    {
                        ctx.builder.build_int_compare(
                            IntPredicate::ULE,
                            int_size,
                            ptr_size,
                            "int_fits",
                        )
                    },
                    |ctx| {
                        ctx.builder.build_int_to_ptr(
                            val.into_int_value(),
                            ctx.voidptr().into_pointer_type(),
                            "int_cast",
                        )
                    },
                    |ctx| {
                        // It needs to be word-aligned, but if `size` is a power of two, it must be either <= word_size or a multiple of the word size
                        assert!(
                            size.is_power_of_two(),
                            "Ty::Int may only be used with power-of-two bit widths, not {}",
                            size
                        );
                        let ptr = ctx.alloca(int_size);
                        let ptr_cast = ctx.builder.build_bitcast(
                            ptr,
                            int_type.ptr_type(AddressSpace::Generic),
                            "_ptr_cast",
                        );
                        let s = ctx.builder.build_store(ptr_cast.into_pointer_value(), val);
                        s.set_alignment(8).unwrap();
                        ptr
                    },
                )
            }
            Ty::Dyn(_) | Ty::Struct(_) | Ty::Fun | Ty::Cont => val.into_pointer_value(),
        }
    }

    /// About how types are stored:
    /// Generally, a type will be stored as its `llvm()` value on the LLVM stack/registers.
    /// When we pass function parameters, we pass it as an `i8*`, calling `to_void_ptr()` and `from_void_ptr()` to convert between.
    /// That way, when we're inside a function, it's back to its `llvm()` type.
    /// In compound types like structs, we store the data inline, each value aligned to a word.
    /// For dynamically sized types like closures, strings, etc., this function returns `-1`,
    /// which conveniently compares as bigger than word size.
    fn normal_size<'a>(&self, ctx: &CodegenCtx<'a>) -> IntValue<'a> {
        match self {
            Ty::Int(_) => self.llvm(ctx).size_of().unwrap(),
            Ty::Struct(v) => {
                let mut total_size = ctx.context.i64_type().const_zero();
                let word_size = ctx.voidptr().size_of().unwrap();
                for i in v {
                    // We align each value to a word, so if it's less than a word we round up
                    let size = i.normal_size(ctx);
                    let smaller_than_word = ctx.builder.build_int_compare(
                        IntPredicate::ULT,
                        size,
                        word_size,
                        "smaller_than_word",
                    );
                    let size = ctx
                        .builder
                        .build_select(smaller_than_word, word_size, size, "rounded_size")
                        .into_int_value();
                    total_size = ctx.builder.build_int_add(total_size, size, "struct_size");
                }
                total_size
            }
            Ty::Dyn(v) => ctx.locals.get(v).unwrap().into_int_value(),
            Ty::Fun | Ty::Cont => ctx
                .context
                .i64_type()
                .const_int(unsafe { std::mem::transmute::<i64, u64>(-1) }, false),
        }
    }

    /// If a type returns `true` here, it must be represented by a simple pointer.
    /// This doesn't guarantee it's dyn size, that's determined by whether `normal_size()` is `-1` (at runtime).
    fn might_be_dyn_size(&self) -> bool {
        match self {
            Ty::Int(_) => false,
            Ty::Fun => true,
            Ty::Cont => true,
            Ty::Struct(_) => true,
            Ty::Dyn(_) => true,
        }
    }

    fn size_of<'a>(&self, val: BasicValueEnum<'a>, ctx: &CodegenCtx<'a>) -> IntValue<'a> {
        let normal_size = self.normal_size(ctx);
        if !self.might_be_dyn_size() {
            return normal_size;
        }
        let minus_one = ctx
            .context
            .i64_type()
            .const_int(unsafe { std::mem::transmute::<i64, u64>(-1) }, false);
        let is_dyn_size =
            ctx.builder
                .build_int_compare(IntPredicate::EQ, normal_size, minus_one, "is_dyn_size");
        ctx.if_else(
            is_dyn_size,
            |ctx| {
                // Since `might_be_dyn_size` is true, we know it's represented as a pointer and we can bitcast it
                let casted = ctx.builder.build_bitcast(
                    val,
                    ctx.context.i64_type().ptr_type(AddressSpace::Generic),
                    "size_ptr",
                );
                let size = ctx
                    .builder
                    .build_load(casted.into_pointer_value(), "dyn_size");
                size.into_int_value()
            },
            |_| normal_size,
        )
    }

    /// If this is stored on the Pika stack, reallocate it to a new location.
    /// Makes sure we can freely `alloca` without erasing wherever this is stored.
    fn reallocate<'a>(
        &self,
        val: BasicValueEnum<'a>,
        ctx: &mut CodegenCtx<'a>,
    ) -> BasicValueEnum<'a> {
        match self {
            Ty::Int(_) => val,
            Ty::Fun | Ty::Cont | Ty::Dyn(_) | Ty::Struct(_) => {
                let size = self.size_of(val, ctx);
                let ptr = ctx.alloca(size);
                self.copy_to(val, ptr, ctx);
                ptr.as_basic_value_enum()
            }
        }
    }

    fn copy_to<'a>(
        &self,
        val: BasicValueEnum<'a>,
        ptr: PointerValue<'a>,
        ctx: &mut CodegenCtx<'a>,
    ) {
        // We do:
        // if size_of<self>() <= size_of<i8*>() {
        //   store(this, ptr)
        // } else {
        //   memcpy(this, ptr)
        // }
        // LLVM should optimize out the conditional easily.
        let this_size = self.size_of(val, ctx);
        let norm_size = self.normal_size(ctx);
        let ptr_size = ctx.voidptr().size_of().unwrap();
        let val = self.to_void_ptr(val, ctx);

        ctx.if_else(
            {
                ctx.builder
                    .build_int_compare(IntPredicate::ULE, norm_size, ptr_size, "fits")
            },
            |ctx| {
                let casted = ctx.builder.build_bitcast(
                    ptr,
                    ctx.voidptr().ptr_type(AddressSpace::Generic),
                    "ptr_cast",
                );
                let s = ctx.builder.build_store(casted.into_pointer_value(), val);
                s.set_alignment(8).unwrap();
                // We need to return a BasicValueEnum for `if_else()`
                ctx.context.bool_type().const_zero().as_basic_value_enum()
            },
            |ctx| {
                ctx.builder
                    .build_memmove(ptr, 8, val, 8, this_size)
                    .unwrap();
                ctx.context.bool_type().const_zero().as_basic_value_enum()
            },
        );
    }

    fn load_from<'a>(&self, ptr: PointerValue<'a>, ctx: &CodegenCtx<'a>) -> BasicValueEnum<'a> {
        // We do:
        // if size_of<self>() <= size_of<i8*>() {
        //   load(ptr)
        // } else {
        //   ptr
        // }
        // LLVM should optimize out the conditional easily.
        let this_size = self.normal_size(ctx);
        let ptr_size = ctx.voidptr().size_of().unwrap();

        let voidptr = ctx.if_else(
            {
                ctx.builder
                    .build_int_compare(IntPredicate::ULE, this_size, ptr_size, "fits")
            },
            |ctx| {
                let casted = ctx.builder.build_bitcast(
                    ptr,
                    ctx.voidptr().ptr_type(AddressSpace::Generic),
                    "ptr_cast",
                );
                ctx.builder
                    .build_load(casted.into_pointer_value(), "load")
                    .into_pointer_value()
            },
            |_| ptr,
        );
        self.from_void_ptr(voidptr, ctx)
    }

    pub fn llvm<'a>(&self, ctx: &CodegenCtx<'a>) -> BasicTypeEnum<'a> {
        match self {
            Ty::Int(i) => ctx.context.custom_width_int_type(*i).as_basic_type_enum(),
            Ty::Dyn(_) | Ty::Struct(_) | Ty::Fun | Ty::Cont => ctx.voidptr(),
            // Ty::Fun => {
            //     ctx.context.struct_type(
            //     &[
            //         ctx.voidptr(),
            //         ctx.context.void_type().fn_type(&[ctx.voidptr(), ctx.voidptr(), ctx.voidptr(), Ty::Cont.llvm(ctx)], false).ptr_type(AddressSpace::Generic).as_basic_type_enum(),
            //         ],
            //     false,
            //     ).as_basic_type_enum()
            // }
            // Ty::Cont => {
            //     ctx.context.struct_type(
            //     &[
            //         ctx.voidptr(),
            //         ctx.context.void_type().fn_type(&[ctx.voidptr(), ctx.voidptr()], false).ptr_type(AddressSpace::Generic).as_basic_type_enum(),
            //         ],
            //     false,
            //     ).as_basic_type_enum()
            // }
        }
    }
}

fn llvm_struct<'a>(values: &[BasicValueEnum<'a>], ctx: &CodegenCtx<'a>) -> StructValue<'a> {
    let types: Vec<_> = values.iter().map(|x| x.get_type()).collect();
    let mut struct_val = ctx.context.struct_type(&types, false).get_undef();
    for (i, v) in values.iter().enumerate() {
        struct_val = ctx
            .builder
            .build_insert_value(struct_val, *v, i as u32, "struct")
            .unwrap()
            .into_struct_value();
    }
    struct_val
}

/// Store, on the stack, something like: `{ i64 %size, void (i8* %env, i8* %sp, args...)* %ptr, upvalues... }`
/// and then return a pointer to it.
/// If `is_cont` is true, we instead store the stack pointer in the closure environment, and don't add a stack pointer argument.
fn llvm_closure<'a>(
    args: &[(Val, &Ty)],
    upvalues: &[(Val, Ty)],
    body: &Low,
    ctx: &mut CodegenCtx<'a>,
    is_cont: bool,
) -> BasicValueEnum<'a> {
    // Stack-allocate the environment and then pass a pointer to it around
    // We always store the size of the environment as the first value, and then the function pointer
    let i64_size = ctx.context.i64_type().size_of();
    let word_size = ctx.voidptr().size_of().unwrap();
    let header_size = ctx.builder.build_int_add(i64_size, word_size, "env_size");
    let mut total_size = header_size;
    // If it's a continuation, the closure environment includes the stack pointer
    if is_cont {
        total_size = ctx.builder.build_int_add(total_size, word_size, "env_size");
    }
    // Add all the sizes of the upvalues
    let upvalues: Vec<_> = upvalues
        .into_iter()
        .map(|(name, ty)| {
            let val = *ctx.locals.get(name).unwrap();
            let size = ty.size_of(val, ctx);
            // We align each value to a word, so if it's less than a word we round up
            let smaller_than_word = ctx.builder.build_int_compare(
                IntPredicate::ULT,
                size,
                word_size,
                "smaller_than_word",
            );
            let size = ctx
                .builder
                .build_select(smaller_than_word, word_size, size, "rounded_size")
                .into_int_value();
            (*name, val, ty, size)
        })
        .collect();
    for (_, _, _, size) in &upvalues {
        total_size = ctx.builder.build_int_add(total_size, *size, "env_size");
    }

    // Now we generate the new function

    let fun = {
        // Store the old block and stack pointer
        let block = ctx.builder.get_insert_block().unwrap();
        let old_stack_ptr = ctx.stack_ptr;

        // All functions, continuation or not, return void, and take an environment as their first argument
        // Non-continuations also take the current stack pointer as their second argument
        let arg_tys: Vec<_> = std::iter::repeat(ctx.voidptr())
            .take(if is_cont { 1 } else { 2 })
            .chain(args.iter().enumerate().map(
                |(i, (_, t))| ctx.voidptr(), // // If it isn't a continuation, the last argument is a continuation, NOT a void pointer
                                             // // Otherwise it is a void pointer
                                             // if !is_cont && i + 1 == args.len() {
                                             //     t.llvm(ctx)
                                             // } else {
                                             //     ctx.voidptr()
                                             // }
            ))
            .collect();
        let ty = ctx.context.void_type().fn_type(&arg_tys, false);
        let fun =
            ctx.module
                .add_function(if is_cont { "_cont_closure" } else { "_closure" }, ty, None);
        fun.set_call_conventions(TAILCC);
        let entry = ctx.context.append_basic_block(fun, "entry");
        ctx.builder.position_at_end(entry);

        // Extract everything we stored in the environment
        let local_env = fun.get_first_param().unwrap().into_pointer_value();
        // We don't need the size or function pointer ourselves, so we can skip it
        let mut slot_ptr = unsafe {
            ctx.builder
                .build_gep(local_env, &[header_size], "env_slots")
        };

        // Load the stack pointer again, or grab that parameter if it's not a continuation
        if is_cont {
            let casted = ctx.builder.build_bitcast(
                slot_ptr,
                ctx.voidptr().ptr_type(AddressSpace::Generic),
                "stack_ptr_slot",
            );
            ctx.stack_ptr = ctx
                .builder
                .build_load(casted.into_pointer_value(), "stack_ptr_saved")
                .into_pointer_value();
            slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[word_size], "next_slot") };
        } else {
            ctx.stack_ptr = fun.get_nth_param(1).unwrap().into_pointer_value();
        }

        // Add upvalues to local environment
        let mut replace = Vec::new();
        for (name, _, ty, _) in &upvalues {
            let val = ty.load_from(slot_ptr, ctx);
            if let Some(old) = ctx.locals.insert(*name, val.as_basic_value_enum()) {
                replace.push((*name, old));
            }

            // Advance by `size` to the next slot
            // We recalculate size here since we're in a different function
            let size = ty.size_of(val, ctx);
            // We align each value to a word, so if it's less than a word we round up
            let smaller_than_word = ctx.builder.build_int_compare(
                IntPredicate::ULT,
                size,
                word_size,
                "smaller_than_word",
            );
            let size = ctx
                .builder
                .build_select(smaller_than_word, word_size, size, "rounded_size")
                .into_int_value();
            slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[size], "next_slot") };
        }

        // Add the parameters to the environment
        for (i, (arg, ty)) in args.iter().enumerate() {
            // We add 2 since the first 2 parameters are always the closure environment and stack pointer
            let param = fun
                .get_nth_param(i as u32 + if is_cont { 1 } else { 2 })
                .unwrap();
            let param = ty.from_void_ptr(param.into_pointer_value(), ctx);
            let param = if is_cont {
                // The value may have been allocated in the caller's stack frame, which we just popped.
                ty.reallocate(param, ctx)
            } else {
                // If this isn't a continuation, it doesn't matter since we're not popping the caller's stack frame
                param
            };
            // // If it isn't a continuation, the last argument is a continuation, NOT a void pointer
            // // Otherwise its a void pointer, and we need to extract the right type
            // let param = if !is_cont && i + 1 == args.len() {
            //     param
            // } else {
            //     ty.from_void_ptr(param, ctx)
            // };
            ctx.locals.insert(*arg, param);
        }

        body.llvm(ctx);

        // Go back back to where we were
        ctx.builder.position_at_end(block);
        ctx.stack_ptr = old_stack_ptr;
        ctx.locals.extend(replace);
        fun
    };

    // Back to creating the closure

    // Allocate space for the whole struct, then insert each element
    let base_ptr = ctx.alloca(total_size);

    // Start with the total size
    {
        let casted = ctx.builder.build_bitcast(
            base_ptr,
            ctx.context.i64_type().ptr_type(AddressSpace::Generic),
            "env_size_slot",
        );
        let s = ctx
            .builder
            .build_store(casted.into_pointer_value(), total_size);
        s.set_alignment(8).unwrap();
    }

    // Then the function pointer
    let slot_ptr = unsafe { ctx.builder.build_gep(base_ptr, &[i64_size], "env_slots") };
    {
        let casted = ctx.builder.build_bitcast(
            slot_ptr,
            fun.get_type()
                .ptr_type(AddressSpace::Generic)
                .ptr_type(AddressSpace::Generic),
            "fun_ptr_slot",
        );
        let s = ctx.builder.build_store(
            casted.into_pointer_value(),
            fun.as_global_value().as_pointer_value(),
        );
        s.set_alignment(8).unwrap();
    }

    // Then the stack pointer, if this is a continuation
    let mut slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[word_size], "env_slots") };
    if is_cont {
        let casted = ctx.builder.build_bitcast(
            slot_ptr,
            ctx.voidptr().ptr_type(AddressSpace::Generic),
            "stack_ptr_slot",
        );
        let s = ctx
            .builder
            .build_store(casted.into_pointer_value(), ctx.stack_ptr);
        s.set_alignment(8).unwrap();
        slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[word_size], "next_slot") };
    }

    // And finally, the upvalues
    for (_, val, ty, size) in &upvalues {
        ty.copy_to(*val, slot_ptr, ctx);

        // Advance by `size` to the next slot
        slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[*size], "next_slot") };
    }

    // Then return the pointer
    base_ptr.as_basic_value_enum()
}

impl Expr {
    fn llvm<'a>(&self, ctx: &mut CodegenCtx<'a>) -> BasicValueEnum<'a> {
        match self {
            Expr::IntConst(size, i) => ctx
                .context
                .custom_width_int_type(*size)
                .const_int(*i, false)
                .as_basic_value_enum(),
            Expr::IntOp(x, op, y) => {
                let x = ctx.locals.get(x).unwrap().into_int_value();
                let y = ctx.locals.get(y).unwrap().into_int_value();
                match op {
                    IntOp::Add => ctx.builder.build_int_add(x, y, "add"),
                    IntOp::Sub => ctx.builder.build_int_sub(x, y, "sub"),
                    IntOp::Mul => ctx.builder.build_int_mul(x, y, "mul"),
                    IntOp::Div => ctx.builder.build_int_signed_div(x, y, "div"),
                }
                .as_basic_value_enum()
            }
            Expr::Val(v) => *ctx.locals.get(v).unwrap(),
            Expr::Struct(v) => {
                // Because the sizes of the struct members might not be known at compile time,
                // we build the struct on the Pika stack and return a pointer
                let mut total_size = ctx.context.i64_type().const_zero();
                let v: Vec<_> = v
                    .iter()
                    .map(|(val, ty)| {
                        let val = *ctx.locals.get(val).unwrap();
                        let size = ty.size_of(val, ctx);
                        (val, ty, size)
                    })
                    .collect();
                for (_, _, size) in &v {
                    total_size = ctx.builder.build_int_add(total_size, *size, "struct_size");
                }

                // Allocate space for the whole struct, then insert each element
                let struct_ptr = ctx.alloca(total_size);
                let mut slot_ptr = struct_ptr;
                for (val, ty, size) in v {
                    ty.copy_to(val, slot_ptr, ctx);
                    // Advance by `size` to the next slot
                    slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[size], "next_slot") };
                }
                struct_ptr.as_basic_value_enum()
            }
            Expr::Project(ty, r, m) => {
                if let Ty::Struct(v) = ty {
                    let struct_ptr = *ctx.locals.get(r).unwrap();
                    let mut slot_ptr = struct_ptr.into_pointer_value();
                    for ty in v.iter().take(*m as usize) {
                        let val = ty.from_void_ptr(slot_ptr, ctx);
                        let size = ty.size_of(val, ctx);
                        // Advance by `size` to the next slot
                        slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[size], "next_slot") };
                    }
                    v[*m as usize].load_from(slot_ptr, ctx)
                } else {
                    unreachable!("A `Project`'s lhs should always be of a known struct type!")
                }
            }
            Expr::Cont {
                arg,
                arg_ty,
                body,
                upvalues,
            } => {
                // Continuations only take one argument
                llvm_closure(&[(*arg, arg_ty)], upvalues, body, ctx, true)
            }
            Expr::Fun {
                arg,
                arg_ty,
                cont,
                cont_ty,
                body,
                upvalues,
            } => {
                // Functions take a continuation as the last argument, in addition to their normal argumnt
                llvm_closure(
                    &[(*arg, arg_ty), (*cont, cont_ty)],
                    upvalues,
                    body,
                    ctx,
                    false,
                )
            }
        }
    }
}

impl Low {
    /// Must emit a terminator
    pub fn llvm(&self, ctx: &mut CodegenCtx) {
        match self {
            Low::Let(name, val, rest) => {
                let val = val.llvm(ctx);
                ctx.locals.insert(*name, val);
                rest.llvm(ctx)
            }
            Low::Global(name, k) => {
                let k = *ctx.locals.get(k).unwrap();

                // Note that this is NOT a closure
                let fun = ctx.module.get_function(&name).unwrap();

                let v =
                    ctx.builder
                        .build_call(fun, &[ctx.stack_ptr.as_basic_value_enum(), k], "_void");
                v.set_call_convention(TAILCC);
                v.set_tail_call(true);
                ctx.builder.build_return(None);
            }
            Low::Call(f, ty, x, k) => {
                let x = *ctx.locals.get(x).unwrap();
                let x = ty.to_void_ptr(x, ctx);
                let k = *ctx.locals.get(k).unwrap();

                // Extract the function pointer from the closure
                let closure = ctx.locals.get(f).unwrap().into_pointer_value();
                let i64_size = ctx.context.i64_type().size_of();
                let f_ptr = unsafe { ctx.builder.build_gep(closure, &[i64_size], "fun_ptr_slot") };
                let f_ptr = ctx
                    .builder
                    .build_bitcast(
                        f_ptr,
                        ctx.context
                            .void_type()
                            .fn_type(
                                &[ctx.voidptr(), ctx.voidptr(), ctx.voidptr(), ctx.voidptr()],
                                false,
                            )
                            .ptr_type(AddressSpace::Generic)
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum(),
                        "fun_ptr_ptr",
                    )
                    .into_pointer_value();
                let f_ptr = ctx
                    .builder
                    .build_load(f_ptr, "fun_ptr")
                    .into_pointer_value();

                let v = ctx.builder.build_call(
                    f_ptr,
                    &[
                        closure.as_basic_value_enum(),
                        ctx.stack_ptr.as_basic_value_enum(),
                        x.as_basic_value_enum(),
                        k,
                    ],
                    "_void",
                );
                v.set_call_convention(TAILCC);
                v.set_tail_call(true);
                ctx.builder.build_return(None);
            }
            Low::ContCall(k, ty, x) => {
                let x = *ctx.locals.get(x).unwrap();
                let x = ty.to_void_ptr(x, ctx);

                // Extract the function pointer from the closure
                let closure = ctx.locals.get(k).unwrap().into_pointer_value();
                let i64_size = ctx.context.i64_type().size_of();
                let f_ptr = unsafe { ctx.builder.build_gep(closure, &[i64_size], "cont_ptr_slot") };
                let f_ptr = ctx
                    .builder
                    .build_bitcast(
                        f_ptr,
                        ctx.context
                            .void_type()
                            .fn_type(&[ctx.voidptr(), ctx.voidptr()], false)
                            .ptr_type(AddressSpace::Generic)
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum(),
                        "cont_ptr_ptr",
                    )
                    .into_pointer_value();
                let f_ptr = ctx
                    .builder
                    .build_load(f_ptr, "cont_ptr")
                    .into_pointer_value();

                let v = ctx.builder.build_call(
                    f_ptr,
                    &[closure.as_basic_value_enum(), x.as_basic_value_enum()],
                    "_void",
                );
                v.set_call_convention(TAILCC);
                v.set_tail_call(true);

                ctx.builder.build_return(None);
            }
            Low::Halt(v) => {
                ctx.builder
                    .build_call(ctx.halt, &[*ctx.locals.get(v).unwrap()], "halt");
                ctx.builder.build_return(None);
            }
        }
    }
}
