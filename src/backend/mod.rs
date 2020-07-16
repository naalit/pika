//! Pika's backend; see README.md in this folder for details.
mod codegen;
pub mod low;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LowDef {
    pub name: String,
    pub cont: low::Val,
    pub cont_ty: low::Ty,
    pub body: low::Low,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct LowMod {
    pub name: String,
    pub defs: Vec<LowDef>,
    pub main: Option<String>,
}

#[no_mangle]
pub extern "C" fn _pika_print_int(i: i32) {
    println!("{}", i);
}

extern "C" {
    pub fn malloc(i: usize) -> *const i8;
}

impl LowDef {
    fn declare(&self, ctx: &codegen::CodegenCtx) {
        // Typecheck everything before codegenning anything
        self.body.type_check(self.cont);
        // It takes a continuation, and the stack pointer, but not an environmeent
        let fun_ty = ctx
            .context
            .void_type()
            .fn_type(&[ctx.voidptr(), self.cont_ty.llvm(ctx)], false);
        let fun = ctx.module.add_function(&self.name, fun_ty, None);
        fun.set_call_conventions(codegen::TAILCC);
    }

    fn define(&self, ctx: &mut codegen::CodegenCtx) {
        use inkwell::values::BasicValue;

        // { u64 %12, fun %16 }

        let fun = ctx.module.get_function(&self.name).unwrap();
        let entry = ctx.context.append_basic_block(fun, "entry");
        ctx.builder.position_at_end(entry);
        ctx.stack_ptr = fun.get_first_param().unwrap().into_pointer_value();
        ctx.stack_ptr.set_name("stack_ptr");
        ctx.locals.insert(self.cont, fun.get_nth_param(1).unwrap());
        fun.get_nth_param(1).unwrap().set_name("cont");
        self.body.llvm(ctx);
    }
}

impl LowMod {
    pub fn llvm<'a>(&self, ctx: &'a inkwell::context::Context) -> inkwell::module::Module<'a> {
        let mut ctx = codegen::CodegenCtx::new(ctx);
        ctx.module.set_name(&self.name);
        // We declare all functions first so they can all call each other
        for def in &self.defs {
            def.declare(&ctx);
        }
        for def in &self.defs {
            def.define(&mut ctx);
        }
        if let Some(main) = &self.main {
            let fun = ctx.module.add_function(
                "_start",
                ctx.context.void_type().fn_type(&[], false),
                None,
            );
            let entry = ctx.context.append_basic_block(fun, "entry");
            ctx.builder.position_at_end(entry);
            ctx.allocate_stack();
            let cont = low::next_val();
            let arg = low::next_val();
            let low = low::Low::Let(
                cont,
                low::Expr::Cont {
                    arg,
                    arg_ty: low::Ty::Int(32),
                    upvalues: Vec::new(),
                    body: Box::new(low::Low::Halt(arg)),
                },
                Box::new(low::Low::Global(main.to_string(), cont)),
            );
            low.llvm(&mut ctx);
        }
        ctx.module
    }
}
