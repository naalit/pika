//! The LLVM interface lives here, since its thread-locality and `inkwell`'s lifetimes don't really work with Salsa.
use super::low::*;
use inkwell::{
    attributes::AttributeLoc,
    builder::Builder,
    context::Context,
    module::{Linkage, Module},
    types::*,
    values::*,
    AddressSpace, IntPredicate,
};
use std::{
    collections::HashMap,
    convert::{TryFrom, TryInto},
    fmt::Debug,
};

/// 4KB stack segments
pub const STACK_SEGMENT_SIZE: u64 = 4 * 1024;

// Some calling conventions
pub const TAILCC: u32 = 18;
pub const CCC: u32 = 0;
pub const FASTCC: u32 = 8;

impl FunAttr {
    fn apply<'a>(self, f: FunctionValue<'a>, ctx: &CodegenCtx<'a>) {
        match self {
            FunAttr::Private => f.set_linkage(Linkage::Private),
            _ => f.add_attribute(
                AttributeLoc::Function,
                ctx.context
                    .create_enum_attribute(self.attr_enum().expect("Unknown attribute"), 0),
            ),
        }
    }

    fn attr_enum(self) -> Option<u32> {
        let name = match self {
            FunAttr::AlwaysInline => "alwaysinline",
            FunAttr::Private => return None,
        };
        Some(inkwell::attributes::Attribute::get_named_enum_kind_id(name))
    }
}

/// Represents the state of the Pika stack.
///
/// We pass the stack pointer around, and pop the stack by restoring saved stack pointers.
/// We also need an ending address for the current segment, so we know how much capacity we have.
/// The ending address is a global variable, b/c it doesn't need to be a register.
/// When we save and restore the stack pointer, we also save and restore the ending address.
/// Since the stack is only popped by restoring saved stack pointers, we also restore that ending address.
///
/// #### Deallocating segments
/// We, when restoring a saved ending address, check if it's the same as the current one (i.e. the same segment).
/// If it isn't, we pop segments until it is - each segment stores, at its base, the high and low addresses of the last segment.
pub struct Stack<'ctx> {
    pub stack_low: PointerValue<'ctx>,
    pub stack_high: PointerValue<'ctx>,
    /// The current stack pointer. We thread this through function calls as needed.
    pub stack_ptr: PointerValue<'ctx>,
    /// We maintain the minimum space we're guaranteed to have available on this segment, so we can avoid checking on every alloca.
    pub min_space: u64,
}

/// We need one of these to generate any LLVM code, but not to generate LowIR
pub struct CodegenCtx<'ctx> {
    pub context: &'ctx Context,
    pub builder: Builder<'ctx>,
    pub locals: HashMap<Val, BasicValueEnum<'ctx>>,
    pub module: Module<'ctx>,
    pub halt: FunctionValue<'ctx>,
    pub stack: Stack<'ctx>,
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

        let stack_low = module.add_global(
            context.i8_type().ptr_type(AddressSpace::Generic),
            None,
            "_pika_stack_low",
        );
        stack_low.set_initializer(
            &context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .const_null(),
        );
        let stack_low = stack_low.as_pointer_value();

        let stack_high = module.add_global(
            context.i8_type().ptr_type(AddressSpace::Generic),
            None,
            "_pika_stack_high",
        );
        stack_high.set_initializer(
            &context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .const_null(),
        );
        let stack_high = stack_high.as_pointer_value();

        CodegenCtx {
            context,
            builder: context.create_builder(),
            locals: HashMap::new(),
            module,
            halt,
            stack: Stack {
                stack_low,
                stack_high,
                stack_ptr: context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .const_null(),
                min_space: 0,
            },
        }
    }

    /// Returns the i8* type, which we use as void* for e.g. closure environments
    pub fn voidptr(&self) -> BasicTypeEnum<'ctx> {
        self.context
            .i8_type()
            .ptr_type(AddressSpace::Generic)
            .as_basic_type_enum()
    }

    /// Rounds to the next highest multiple of the word size on this platform
    pub fn round_to_word(&self, size: IntValue<'ctx>) -> IntValue<'ctx> {
        // For now we assume words are 8 bytes
        // TODO use target information or something

        // (size + 7) & ~7
        let seven = self.context.i64_type().const_int(7, false);
        let not_seven = seven.const_not();
        let plus_seven = self.builder.build_int_add(size, seven, "plus_seven");
        let rounded = self
            .builder
            .build_and(plus_seven, not_seven, "rounded_size");
        rounded
    }

    /// `ptr` must have two words of space available
    fn save_stack(&self, ptr: PointerValue<'ctx>) {
        let stack_ptr_ptr = self
            .builder
            .build_bitcast(
                ptr,
                self.voidptr().ptr_type(AddressSpace::Generic),
                "stack_ptr_ptr",
            )
            .into_pointer_value();
        self.builder
            .build_store(stack_ptr_ptr, self.stack.stack_ptr);

        let stack_low_slot = unsafe {
            self.builder
                .build_gep(ptr, &[self.voidptr().size_of().unwrap()], "stack_low_slot")
        };
        let stack_low_ptr = self
            .builder
            .build_bitcast(
                stack_low_slot,
                self.voidptr().ptr_type(AddressSpace::Generic),
                "stack_low_ptr",
            )
            .into_pointer_value();
        let stack_low = self
            .builder
            .build_load(self.stack.stack_low, "stack_low")
            .into_pointer_value();
        self.builder.build_store(stack_low_ptr, stack_low);
    }

    /// Finishes restoring the stack, freeing unneeded stack segments.
    fn finish_restore_stack(
        &mut self,
        (stack_low, old_stack_low): (PointerValue<'ctx>, PointerValue<'ctx>),
    ) {
        let var = self.builder.build_alloca(self.voidptr(), "var");
        self.builder.build_store(var, old_stack_low);

        //   ...load stack pointer and %stack_low...
        //   %var = box %old_stack_low
        //   br %header
        // header:
        //   %old_stack_low = load %var
        //   br (%stack_low == %old_stack_low), %done, %free_segment
        // free_segment:
        //   ; each stack segment stores a pointer to the last one at its base (which is the high address since we bump down)
        //   %previous_stack_low = load (%old_stack_low + STACK_SEGMENT_SIZE - 8)
        //   store %var, %previous_stack_low
        //   call @free(%old_stack_low)
        //   br %header
        // done:
        //   ...continue...

        let header = self.context.insert_basic_block_after(
            self.builder.get_insert_block().unwrap(),
            "header.free_segment",
        );
        let free_segment = self
            .context
            .insert_basic_block_after(header, "free_segment");
        let done = self
            .context
            .insert_basic_block_after(free_segment, "done.free_segment");
        self.builder.build_unconditional_branch(header);

        self.builder.position_at_end(header);
        let old_stack_low = self
            .builder
            .build_load(var, "old_stack_low")
            .into_pointer_value();
        let diff = self
            .builder
            .build_ptr_diff(stack_low, old_stack_low, "diff");
        let same_segment = self.builder.build_int_compare(
            IntPredicate::EQ,
            diff,
            self.context.i64_type().const_zero(),
            "same_segment",
        );
        self.builder
            .build_conditional_branch(same_segment, done, free_segment);

        self.builder.position_at_end(free_segment);
        // self.builder.build_call(self.halt, &[self.context.i32_type().const_int(-2i32 as u64, false).as_basic_value_enum()], "_log_free");

        let prev_ptr = unsafe {
            self.builder.build_gep(
                old_stack_low,
                &[self
                    .context
                    .i64_type()
                    .const_int(STACK_SEGMENT_SIZE - 8, false)],
                "previous_ptr_slot",
            )
        };
        let prev_ptr = self
            .builder
            .build_bitcast(
                prev_ptr,
                self.voidptr().ptr_type(AddressSpace::Generic),
                "previous_ptr",
            )
            .into_pointer_value();
        let previous_stack_low = self.builder.build_load(prev_ptr, "previous_stack_low");
        self.builder.build_store(var, previous_stack_low);
        self.builder.build_free(old_stack_low);
        self.builder.build_unconditional_branch(header);

        self.builder.position_at_end(done);
    }

    /// Loads the saved stack pointer and end.
    ///
    /// It's safe to use the stack after this, but leaks may happen.
    /// Make sure to call `finish_restore_stack()` with the return value to avoid that.
    fn start_restore_stack(
        &mut self,
        ptr: PointerValue<'ctx>,
    ) -> (PointerValue<'ctx>, PointerValue<'ctx>) {
        let stack_ptr_ptr = self
            .builder
            .build_bitcast(
                ptr,
                self.voidptr().ptr_type(AddressSpace::Generic),
                "stack_ptr_ptr",
            )
            .into_pointer_value();
        self.stack.stack_ptr = self
            .builder
            .build_load(stack_ptr_ptr, "stack_ptr_saved")
            .into_pointer_value();

        let stack_low_slot = unsafe {
            self.builder
                .build_gep(ptr, &[self.voidptr().size_of().unwrap()], "stack_low_slot")
        };
        let stack_low_ptr = self
            .builder
            .build_bitcast(
                stack_low_slot,
                self.voidptr().ptr_type(AddressSpace::Generic),
                "stack_low_ptr",
            )
            .into_pointer_value();
        let stack_low = self
            .builder
            .build_load(stack_low_ptr, "stack_low")
            .into_pointer_value();

        let old_stack_low = self
            .builder
            .build_load(self.stack.stack_low, "old_stack_low")
            .into_pointer_value();
        self.builder.build_store(self.stack.stack_low, stack_low);

        // We need to pass `stack_low` along because we could allocate another segment in the meantime and change the global
        (stack_low, old_stack_low)
    }

    /// Allocates and switches to a new stack segment
    fn morestack(&mut self) {
        // self.builder.build_call(self.halt, &[self.context.i32_type().const_int(-1i32 as u64, false).as_basic_value_enum()], "_log_morestack");

        let low = self
            .builder
            .build_array_malloc(
                self.context.i8_type(),
                self.context.i64_type().const_int(STACK_SEGMENT_SIZE, false),
                "stack_low",
            )
            .unwrap();

        // Each stack segment stores a pointer to the last one at its high address
        let high = unsafe {
            self.builder.build_gep(
                low,
                // One word below the top
                &[self
                    .context
                    .i64_type()
                    .const_int(STACK_SEGMENT_SIZE - 8, false)],
                "stack_high",
            )
        };
        let previous_stack_low = self
            .builder
            .build_load(self.stack.stack_low, "previous_stack_low");
        self.builder.build_store(
            self.builder
                .build_bitcast(
                    high,
                    self.voidptr().ptr_type(AddressSpace::Generic),
                    "previous_ptr",
                )
                .into_pointer_value(),
            previous_stack_low,
        );

        self.builder.build_store(self.stack.stack_low, low);
        self.builder.build_store(self.stack.stack_high, high);
        // We bump down, so start at the high value
        self.stack.stack_ptr = high;
        self.stack.min_space = STACK_SEGMENT_SIZE;
    }

    /// Allocate `size` bytes on the Pika stack
    pub fn alloca(&mut self, size: IntValue<'ctx>, max_size: Option<u64>) -> PointerValue<'ctx> {
        let neg_size = self.builder.build_int_neg(size, "minus_size");
        let new_ptr = unsafe {
            self.builder
                .build_gep(self.stack.stack_ptr, &[neg_size], "stack_try_push")
        };

        if let Some(max_size) = max_size {
            if max_size <= self.stack.min_space {
                // If we know we have enough space, we can skip the branching
                // LLVM probably can't figure this out on its own, so we do this ourselves
                self.stack.min_space -= max_size;
                self.stack.stack_ptr = new_ptr;
                return new_ptr;
            } else {
                // We don't even know if this will fit, let alone how much will be left after
                self.stack.min_space = 0;
            }
        }

        let end_ptr = self
            .builder
            .build_load(self.stack.stack_low, "stack_low")
            .into_pointer_value();
        let end_as_int =
            self.builder
                .build_ptr_to_int(end_ptr, self.context.i64_type(), "end_as_int");
        let new_as_int =
            self.builder
                .build_ptr_to_int(new_ptr, self.context.i64_type(), "try_push_as_int");

        let has_space =
            self.builder
                .build_int_compare(IntPredicate::UGE, new_as_int, end_as_int, "has_space");
        self.if_else_mut(
            has_space,
            |ctx| {
                ctx.stack.stack_ptr = new_ptr;
                new_ptr
            },
            |ctx| {
                ctx.morestack();
                // TODO what if `size` is bigger than a segment?
                let new_ptr = unsafe {
                    ctx.builder
                        .build_gep(ctx.stack.stack_ptr, &[neg_size], "stack_push")
                };
                ctx.stack.stack_ptr = new_ptr;
                new_ptr
            },
        )
    }

    /// Frees any remaining segments of the Pika stack.
    fn free_stack(&mut self) {
        let low = self
            .builder
            .build_load(self.stack.stack_low, "stack_low")
            .into_pointer_value();
        // We tell it, "we were here, and we're restoring to `null`, so free everything until there"
        self.finish_restore_stack((self.voidptr().into_pointer_type().const_null(), low));
    }

    /// Allocates the first segment of the Pika stack. Run at the beginning of execution.
    pub fn allocate_stack(&mut self) {
        self.morestack();
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
        let old_stack_ptr = self.stack.stack_ptr;

        let after_block = self.context.insert_basic_block_after(old_block, "merge");

        let yes_block = self
            .context
            .insert_basic_block_after(old_block, "yes_block");
        self.builder.position_at_end(yes_block);
        let yes_val = yes(self);
        let yes_stack_ptr = self.stack.stack_ptr;
        let phi_type = yes_val.as_basic_value_enum().get_type();
        // They could have branched around in `yes()`, so we need to phi from *this* block
        let yes_block_f = self.builder.get_insert_block().unwrap();
        self.builder.build_unconditional_branch(after_block);

        self.stack.stack_ptr = old_stack_ptr;
        let no_block = self.context.insert_basic_block_after(old_block, "no_block");
        self.builder.position_at_end(no_block);
        let no_val = no(self);
        let no_stack_ptr = self.stack.stack_ptr;
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
        self.stack.stack_ptr = stack_ptr_phi.as_basic_value().into_pointer_value();

        phi.as_basic_value().try_into().unwrap()
    }
}

impl Ty {
    /// Does this type have a compile-time-known maximum size? If so, what is it, in bytes?
    fn max_size(&self) -> Option<u64> {
        match self {
            Ty::Int(bits) => Some(*bits as u64 / 8),
            // TODO not assume 64-bit
            Ty::Cont => Some(8),
            Ty::Unit => Some(0),
            Ty::Union(v) => {
                // We always store the size
                let mut max = 8;
                for i in v {
                    max = max.max(i.max_size()?);
                }
                Some(max)
            }
            Ty::Struct(v) => {
                let mut tot = if self.might_be_dyn_size() { 8 } else { 0 };
                for i in v {
                    tot += i.max_size()?;
                }
                Some(tot)
            }
            Ty::Dyn(_) | Ty::Fun | Ty::Unknown => None,
        }
    }

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
            Ty::Unit => ctx
                .context
                .struct_type(&[], false)
                .const_zero()
                .as_basic_value_enum(),
            Ty::Dyn(_) | Ty::Struct(_) | Ty::Fun | Ty::Cont | Ty::Union(_) | Ty::Unknown => {
                ptr.as_basic_value_enum()
            }
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
                        let ptr = ctx.alloca(int_size, Some(*size as u64 / 8));
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
            // We don't care what the voidptr representation of a zero-sized type is, so just use undef
            Ty::Unit => ctx.voidptr().into_pointer_type().get_undef(),
            Ty::Dyn(_) | Ty::Struct(_) | Ty::Fun | Ty::Cont | Ty::Union(_) | Ty::Unknown => {
                val.into_pointer_value()
            }
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
            Ty::Unit => ctx.context.i64_type().const_zero(),
            Ty::Int(_) => self.llvm(ctx).size_of().unwrap(),
            Ty::Struct(v) => {
                // 1-element structs are transparent, but always stored as a void ptr
                if v.len() == 1 {
                    return v[0].normal_size(ctx);
                }

                let mut total_size = ctx.context.i64_type().const_zero();
                let mut any_dyn = ctx.context.bool_type().const_zero();
                let minus_one = ctx.context.i64_type().const_int(-1i64 as u64, false);
                for i in v {
                    let size = i.normal_size(ctx);
                    // If any members are dynamically sized, so is the struct
                    let is_dyn_size = ctx.builder.build_int_compare(
                        IntPredicate::EQ,
                        size,
                        minus_one,
                        "member_is_dyn_size",
                    );
                    any_dyn = ctx
                        .builder
                        .build_or(is_dyn_size, any_dyn, "any_member_dyn_size");
                    // We align each value to a word, so if it's less than a word we round up
                    let size = ctx.round_to_word(size);
                    total_size = ctx.builder.build_int_add(total_size, size, "struct_size");
                }
                ctx.if_else(any_dyn, |_| minus_one, |_| total_size)
            }
            Ty::Dyn(v) => ctx.locals.get(v).unwrap().into_int_value(),
            // We leave continuations in place, don't move them around, because they can't escape their stack region like closures can
            // We just pass around the same pointer
            Ty::Cont => ctx.voidptr().size_of().unwrap(),
            // Closures and unions are always dynamically sized
            Ty::Fun | Ty::Union(_) | Ty::Unknown => {
                ctx.context.i64_type().const_int(-1i64 as u64, false)
            }
        }
    }

    /// If a type returns `true` here, it must be represented by a simple pointer.
    /// This doesn't guarantee it's dyn size, that's determined by whether `normal_size()` is `-1` (at runtime).
    fn might_be_dyn_size(&self) -> bool {
        match self {
            Ty::Int(_) | Ty::Unit | Ty::Cont => false,
            Ty::Struct(v) => v.iter().any(Ty::might_be_dyn_size),
            Ty::Fun | Ty::Dyn(_) | Ty::Union(_) | Ty::Unknown => true,
        }
    }

    fn size_of<'a>(&self, val: BasicValueEnum<'a>, ctx: &CodegenCtx<'a>) -> IntValue<'a> {
        let normal_size = self.normal_size(ctx);
        if !self.might_be_dyn_size() {
            return normal_size;
        }
        let minus_one = ctx.context.i64_type().const_int(-1i64 as u64, false);
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
            Ty::Int(_) | Ty::Unit => val,
            // Again, we never need to reallocate continuations, because they're always called before the stack unwinds past them
            Ty::Cont => val,
            Ty::Struct(v) if v.len() == 1 => v[0].reallocate(val, ctx),
            Ty::Dyn(_) => {
                // If it's smaller than a word, we don't have a pointer, we have a bitcasted something else, so don't copy it
                // That's only true of the normal size, though, not the dynamic syze
                let norm_size = self.normal_size(ctx);
                let size = self.size_of(val, ctx);
                let word_size = ctx.voidptr().size_of().unwrap();
                ctx.if_else_mut(
                    {
                        ctx.builder.build_int_compare(
                            IntPredicate::ULE,
                            norm_size,
                            word_size,
                            "fits",
                        )
                    },
                    |_| val,
                    |ctx| {
                        let ptr = ctx.alloca(size, None);
                        self.copy_to(val, ptr, ctx);
                        ptr.as_basic_value_enum()
                    },
                )
            }
            Ty::Fun | Ty::Struct(_) | Ty::Union(_) | Ty::Unknown => {
                let size = self.size_of(val, ctx);
                let ptr = ctx.alloca(size, self.max_size());
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
        //   if size_of<self>() != 0 {
        //      store(this, ptr)
        //   }
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
                ctx.if_else(
                    {
                        ctx.builder.build_int_compare(
                            IntPredicate::EQ,
                            norm_size,
                            ctx.context.i64_type().const_zero(),
                            "is_zero_sized",
                        )
                    },
                    |ctx| {
                        // We need to return a BasicValueEnum for `if_else()`
                        ctx.context.bool_type().const_zero().as_basic_value_enum()
                    },
                    |ctx| {
                        let casted = ctx.builder.build_bitcast(
                            ptr,
                            ctx.voidptr().ptr_type(AddressSpace::Generic),
                            "ptr_cast",
                        );
                        let s = ctx.builder.build_store(casted.into_pointer_value(), val);
                        s.set_alignment(8).unwrap();
                        ctx.context.bool_type().const_zero().as_basic_value_enum()
                    },
                )
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
        // if size_of<self>() <= size_of<i8*>() && size_of<self>() > 0 {
        //   load(ptr)
        // } else {
        //   ptr
        // }
        // LLVM should optimize out the conditional easily.
        let this_size = self.normal_size(ctx);
        let ptr_size = ctx.voidptr().size_of().unwrap();

        let voidptr = ctx.if_else(
            {
                let fits =
                    ctx.builder
                        .build_int_compare(IntPredicate::ULE, this_size, ptr_size, "fits");
                let non_zero = ctx.builder.build_int_compare(
                    IntPredicate::UGT,
                    this_size,
                    ctx.context.i64_type().const_zero(),
                    "non_zero_sized",
                );
                ctx.builder.build_and(fits, non_zero, "should_load")
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

    fn llvm<'a>(&self, ctx: &CodegenCtx<'a>) -> BasicTypeEnum<'a> {
        match self {
            Ty::Unit => ctx.context.struct_type(&[], false).as_basic_type_enum(),
            Ty::Int(i) => ctx.context.custom_width_int_type(*i).as_basic_type_enum(),
            Ty::Dyn(_) | Ty::Struct(_) | Ty::Fun | Ty::Cont | Ty::Union(_) | Ty::Unknown => {
                ctx.voidptr()
            }
        }
    }
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
    // TODO not assume 64-bit
    let mut max_size = Some(16);
    let mut total_size = header_size;
    // If it's a continuation, the closure environment includes the stack pointer and the stack end
    if is_cont {
        total_size = ctx.builder.build_int_add(total_size, word_size, "env_size");
        total_size = ctx.builder.build_int_add(total_size, word_size, "env_size");
        max_size = max_size.map(|x| x + 16);
    }
    // Add all the sizes of the upvalues
    let upvalues: Vec<_> = upvalues
        .into_iter()
        .map(|(name, ty)| {
            let val = *ctx.locals.get(name).unwrap();
            let size = ty.size_of(val, ctx);
            // We align each value to a word, so if it's less than a word we round up
            let size = ctx.round_to_word(size);
            (*name, val, ty, size)
        })
        .collect();
    for (_, _, t, size) in &upvalues {
        total_size = ctx.builder.build_int_add(total_size, *size, "env_size");
        max_size = max_size.and_then(|x| t.max_size().map(|y| x + y));
    }

    // Now we generate the new function

    let fun = {
        // Store the old block and stack pointer
        let block = ctx.builder.get_insert_block().unwrap();
        let old_stack_ptr = ctx.stack.stack_ptr;
        let old_min_space = ctx.stack.min_space;

        // All functions, continuation or not, return void, and take an environment as their first argument
        // Non-continuations also take the current stack pointer as their second argument
        let arg_tys: Vec<_> = std::iter::repeat(ctx.voidptr())
            .take(if is_cont { 1 } else { 2 } + args.len())
            .collect();
        let ty = ctx.context.void_type().fn_type(&arg_tys, false);
        let mut name = block
            .get_parent()
            .unwrap()
            .get_name()
            .to_str()
            .unwrap()
            .to_string();
        if is_cont {
            if !name.ends_with("._continuation") {
                name.push_str("._continuation");
            }
        } else {
            name.push_str("._closure");
        }
        let fun = ctx.module.add_function(&name, ty, None);
        fun.set_call_conventions(TAILCC);
        // We make all continuations `private`, that might help LLVM optimize CPS better
        if is_cont {
            FunAttr::Private.apply(fun, ctx);
        }

        let entry = ctx.context.append_basic_block(fun, "entry");
        ctx.builder.position_at_end(entry);

        // Extract everything we stored in the environment
        let local_env = fun.get_first_param().unwrap().into_pointer_value();
        local_env.set_name("env");
        // We don't need the size or function pointer ourselves, so we can skip it
        let mut slot_ptr = unsafe {
            ctx.builder
                .build_gep(local_env, &[header_size], "env_slots")
        };

        // Load the stack pointer again, or grab that parameter if it's not a continuation
        let token = if is_cont {
            // We *don't* call `finish_restore_stack()`, because the parameters might be stored
            //  in another stack segment and we don't want to free it until we've reallocated them
            let token = ctx.start_restore_stack(slot_ptr);
            slot_ptr = unsafe {
                ctx.builder
                    .build_gep(slot_ptr, &[word_size], "_next_slot_partial")
            };
            slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[word_size], "next_slot") };
            Some(token)
        } else {
            ctx.stack.stack_ptr = fun.get_nth_param(1).unwrap().into_pointer_value();
            ctx.stack.stack_ptr.set_name("stack_ptr");
            // We got the stack pointer in from outside, who knows how much space is left?
            // It might be a good idea eventually to maintain a minimum guaranteed size across calls,
            // so functions that don't allocate much called in a loop don't have to do any checks.
            ctx.stack.min_space = 0;
            None
        };

        // Add upvalues to local environment
        let mut replace = Vec::new();
        for (name, _, ty, _) in &upvalues {
            let val = ty.load_from(slot_ptr, ctx);
            if let Some(old) = ctx.locals.insert(*name, val) {
                replace.push((*name, old));
            }

            // Advance by `size` to the next slot
            // We recalculate size here since we're in a different function
            let size = ty.size_of(val, ctx);
            // We align each value to a word, so if it's less than a word we round up
            let size = ctx.round_to_word(size);
            slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[size], "next_slot") };
        }

        // Add the parameters to the environment
        for (i, (arg, ty)) in args.iter().enumerate() {
            // We add 2 since the first 2 parameters are always the closure environment and stack pointer
            let param = fun
                .get_nth_param(i as u32 + if is_cont { 1 } else { 2 })
                .unwrap();
            if !is_cont && i == 1 {
                param.set_name("cont");
            } else {
                param.set_name("arg");
            }
            let param = ty.from_void_ptr(param.into_pointer_value(), ctx);
            let param = if is_cont {
                // The value may have been allocated in the caller's stack frame, which we just popped.
                ty.reallocate(param, ctx)
            } else {
                // If this isn't a continuation, it doesn't matter since we're not popping the caller's stack frame
                param
            };
            ctx.locals.insert(*arg, param);
        }

        // Now that we've reallocated the parameters, we can do this
        if let Some(token) = token {
            ctx.finish_restore_stack(token);
        }

        body.llvm(ctx);

        // Go back back to where we were
        ctx.builder.position_at_end(block);
        ctx.stack.stack_ptr = old_stack_ptr;
        ctx.stack.min_space = old_min_space;
        ctx.locals.extend(replace);
        fun
    };

    // Back to creating the closure

    // Allocate space for the whole struct, then insert each element
    let base_ptr = ctx.alloca(total_size, max_size);

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
        ctx.save_stack(slot_ptr);
        slot_ptr = unsafe {
            ctx.builder
                .build_gep(slot_ptr, &[word_size], "_next_slot_partial")
        };
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
            Expr::Unit => ctx
                .context
                .struct_type(&[], false)
                .const_zero()
                .as_basic_value_enum(),
            Expr::IntConst(size, i) => ctx
                .context
                .custom_width_int_type(*size)
                .const_int(*i, false)
                .as_basic_value_enum(),
            Expr::CompOp(x, op, y) => {
                let x = ctx.locals.get(x).unwrap().into_int_value();
                let y = ctx.locals.get(y).unwrap().into_int_value();
                match op {
                    CompOp::Eq => ctx.builder.build_int_compare(IntPredicate::EQ, x, y, "eq"),
                }
                .as_basic_value_enum()
            }
            Expr::IntOp(x, op, y) => {
                let x = ctx.locals.get(x).unwrap().into_int_value();
                let y = ctx.locals.get(y).unwrap().into_int_value();
                match op {
                    IntOp::Add => ctx.builder.build_int_add(x, y, "add"),
                    IntOp::Sub => ctx.builder.build_int_sub(x, y, "sub"),
                    IntOp::Mul => ctx.builder.build_int_mul(x, y, "mul"),
                    IntOp::Div => ctx.builder.build_int_signed_div(x, y, "div"),
                    IntOp::BitAnd => ctx.builder.build_and(x, y, "bitwise_and"),
                    IntOp::BitOr => ctx.builder.build_or(x, y, "bitwise_or"),
                }
                .as_basic_value_enum()
            }
            Expr::Val(v) => *ctx.locals.get(v).unwrap(),
            Expr::Variant(t, v, i) => {
                let t = if let Ty::Union(v) = t {
                    v[*i as usize].clone()
                } else {
                    unreachable!()
                };
                let v = *ctx.locals.get(v).unwrap();

                // I don't think we need word alignment here since we don't store anything after the variant, but it's possible
                let size = t.size_of(v, ctx);

                let size = ctx.builder.build_int_add(
                    size,
                    ctx.context.i64_type().size_of(),
                    "variant_size",
                );
                let ptr = ctx.alloca(size, t.max_size());

                let casted = ctx
                    .builder
                    .build_bitcast(
                        ptr,
                        ctx.context.i64_type().ptr_type(AddressSpace::Generic),
                        "variant_size_ptr",
                    )
                    .into_pointer_value();
                ctx.builder.build_store(casted, size);
                let payload_slot = unsafe {
                    ctx.builder
                        .build_gep(ptr, &[ctx.context.i64_type().size_of()], "payload_slot")
                };
                t.copy_to(v, payload_slot, ctx);

                ptr.as_basic_value_enum()
            }
            Expr::AsVariant(t, u, i) => {
                let t = if let Ty::Union(v) = t {
                    v[*i as usize].clone()
                } else {
                    unreachable!()
                };
                let ptr = ctx.locals.get(u).unwrap().into_pointer_value();
                let payload_slot = unsafe {
                    ctx.builder
                        .build_gep(ptr, &[ctx.context.i64_type().size_of()], "payload_slot")
                };
                t.load_from(payload_slot, ctx)
            }
            Expr::Struct(v) => {
                // Structs with 1 element are transparent, but stored as a void ptr
                // So to create one, just call `to_void_ptr()` on the element.
                if v.len() == 1 {
                    return v[0]
                        .1
                        .to_void_ptr(*ctx.locals.get(&v[0].0).unwrap(), ctx)
                        .as_basic_value_enum();
                }

                let minus_one = ctx.context.i64_type().const_int(-1i64 as u64, false);
                let mut any_dyn = ctx.context.bool_type().const_zero();

                // Because the sizes of the struct members might not be known at compile time,
                // we build the struct on the Pika stack and return a pointer
                let mut total_size = ctx.context.i64_type().const_zero();
                let mut max_size = Some(0);
                let mut maybe_dyn = false;
                let v: Vec<_> = v
                    .iter()
                    .map(|(val, ty)| {
                        let val = *ctx.locals.get(val).unwrap();
                        let norm_size = ty.normal_size(ctx);
                        let size = if ty.might_be_dyn_size() {
                            let is_dyn_size = ctx.builder.build_int_compare(
                                IntPredicate::EQ,
                                norm_size,
                                minus_one,
                                "member_is_dyn_size",
                            );
                            any_dyn =
                                ctx.builder
                                    .build_or(is_dyn_size, any_dyn, "any_member_dyn_size");
                            ty.size_of(val, ctx)
                        } else {
                            norm_size
                        };
                        // We align each value to a word, so if it's less than a word we round up
                        let size = ctx.round_to_word(size);
                        (val, ty, size)
                    })
                    .collect();
                for (_, t, size) in &v {
                    total_size = ctx.builder.build_int_add(total_size, *size, "struct_size");
                    maybe_dyn |= t.might_be_dyn_size();
                    max_size = max_size.and_then(|x| t.max_size().map(|y| x + y));
                }
                if maybe_dyn {
                    max_size.map(|x| x + 8);
                }
                total_size = ctx.if_else(
                    any_dyn,
                    |ctx| {
                        ctx.builder.build_int_add(
                            total_size,
                            ctx.context.i64_type().size_of(),
                            "dyn_struct_size",
                        )
                    },
                    |_| total_size,
                );

                // Allocate space for the whole struct, then insert each element
                let struct_ptr = ctx.alloca(total_size, max_size);
                let mut slot_ptr = ctx.if_else(
                    any_dyn,
                    |ctx| {
                        let cast = ctx
                            .builder
                            .build_bitcast(
                                struct_ptr,
                                ctx.context.i64_type().ptr_type(AddressSpace::Generic),
                                "dyn_struct_size_ptr",
                            )
                            .into_pointer_value();
                        ctx.builder.build_store(cast, total_size);
                        unsafe {
                            ctx.builder.build_gep(
                                struct_ptr,
                                &[ctx.context.i64_type().size_of()],
                                "first_slot",
                            )
                        }
                    },
                    |_| struct_ptr,
                );
                for (val, ty, size) in v {
                    ty.copy_to(val, slot_ptr, ctx);
                    // Advance by `size` to the next slot
                    slot_ptr = unsafe { ctx.builder.build_gep(slot_ptr, &[size], "next_slot") };
                }
                struct_ptr.as_basic_value_enum()
            }
            Expr::Project(ty, r, m) => {
                if let Ty::Struct(v) = ty {
                    // Structs with 1 element are transparent, but stored as a void ptr
                    // So to grab that element, just call `from_void_ptr()`.
                    if v.len() == 1 {
                        assert_eq!(*m, 0);
                        return v[0]
                            .from_void_ptr(ctx.locals.get(r).unwrap().into_pointer_value(), ctx);
                    }

                    let mut any_dyn = ctx.context.bool_type().const_zero();
                    let minus_one = ctx.context.i64_type().const_int(-1i64 as u64, false);

                    for ty in v {
                        if ty.might_be_dyn_size() {
                            let norm_size = ty.normal_size(ctx);
                            let is_dyn_size = ctx.builder.build_int_compare(
                                IntPredicate::EQ,
                                norm_size,
                                minus_one,
                                "member_is_dyn_size",
                            );
                            any_dyn =
                                ctx.builder
                                    .build_or(is_dyn_size, any_dyn, "any_member_dyn_size");
                        }
                    }

                    let struct_ptr = *ctx.locals.get(r).unwrap();
                    let slot_ptr = struct_ptr.into_pointer_value();
                    // If the struct is dynamically sized, we need to skip the size slot
                    let mut slot_ptr = ctx.if_else(
                        any_dyn,
                        |ctx| unsafe {
                            ctx.builder.build_gep(
                                slot_ptr,
                                &[ctx.context.i64_type().size_of()],
                                "first_slot",
                            )
                        },
                        |_| slot_ptr,
                    );
                    for ty in v.iter().take(*m as usize) {
                        let val = ty.from_void_ptr(slot_ptr, ctx);
                        let size = ty.size_of(val, ctx);
                        // We align each value to a word, so if it's less than a word we round up
                        let size = ctx.round_to_word(size);
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
                body,
                upvalues,
            } => {
                // Functions take a continuation as the last argument, in addition to their normal argumnt
                llvm_closure(
                    &[(*arg, arg_ty), (*cont, &Ty::Cont)],
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
            Low::IfElse(cond, yes, no) => {
                let cond = ctx.locals.get(cond).unwrap().into_int_value();

                // `CodegenCtx::if_else()` is for expressions, it would be a hassle to use it here, so we just reimplement it
                let old_block = ctx.builder.get_insert_block().unwrap();
                let old_stack_ptr = ctx.stack.stack_ptr;

                let yes_block = ctx.context.insert_basic_block_after(old_block, "then");
                ctx.builder.position_at_end(yes_block);
                yes.llvm(ctx);

                ctx.stack.stack_ptr = old_stack_ptr;
                let no_block = ctx.context.insert_basic_block_after(old_block, "else");
                ctx.builder.position_at_end(no_block);
                no.llvm(ctx);

                ctx.builder.position_at_end(old_block);
                ctx.builder.build_conditional_branch(
                    cond.as_basic_value_enum().into_int_value(),
                    yes_block,
                    no_block,
                );
            }
            Low::Global(name, k) => {
                let k = *ctx.locals.get(k).unwrap();

                // Note that this is NOT a closure
                let fun = ctx.module.get_function(&name).unwrap();

                let v = ctx.builder.build_call(
                    fun,
                    &[ctx.stack.stack_ptr.as_basic_value_enum(), k],
                    "_void",
                );
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
                        ctx.stack.stack_ptr.as_basic_value_enum(),
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
                // We're done, so we can free the stack
                ctx.free_stack();
                ctx.builder.build_return(None);
            }
            Low::Unreachable => {
                ctx.builder.build_unreachable();
            }
        }
    }
}
