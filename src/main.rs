use durin::inkwell::{
    types::{AnyType, BasicType},
    values::BasicValue,
};
use std::fs::File;
use std::io::Read;

pub mod builtins;
pub mod common;
pub mod elaborate;
pub mod error;
pub mod evaluate;
pub mod lexer;
pub mod lower;
pub mod pattern;
pub mod pretty;
pub mod query;
pub mod repl;
pub mod term;
use query::*;

mod parser;

/// For the generated code to call
#[no_mangle]
extern "C" fn print_i32(i: i32) {
    println!("{}", i);
}
extern "C" {
    pub fn malloc(i: usize) -> *const i8;
}

fn main() {
    if let Some(file_name) = std::env::args().nth(1) {
        let mut file = File::open(file_name.clone()).unwrap();
        let mut buf = String::new();
        file.read_to_string(&mut buf).unwrap();
        if !buf.ends_with('\n') {
            buf.push('\n');
        }
        let mut db = Database::default();
        let id = error::FILES.write().unwrap().add(file_name, buf.clone());
        db.set_file_source(id, buf);
        db.check_all(id);
        if db.num_errors() == 0 {
            eprintln!("File elaborated successfully!");
            let mut durin = db.durin(id);
            // eprintln!("Durin module:\n{}", durin.emit());
            let backend = durin::backend::Backend::native();
            let m = backend.codegen_module(&mut durin);
            let cxt = m.get_context();
            // eprintln!("LLVM module:\n{}", m.print_to_string().to_str().unwrap());
            m.verify().unwrap();

            // Run the main function if it exists
            if let Some(f) = m.get_function("main") {
                let ty = f.get_type().print_to_string();
                // Durin might or might not have succeeded in turning `main` into direct style
                let run = match ty.to_str().unwrap() {
                    // () -> () in CPS
                    "void ({}, { i8*, void (i8*, i8*)* })" => true,
                    // () -> () in direct style
                    "{} ({})" => true,
                    t => {
                        eprintln!("Warning: main function has type {}, not calling it", t);
                        false
                    }
                };
                if run {
                    // The main function is tailcc, so we make a new ccc function which just calls it and returns
                    let new_fun =
                        m.add_function("$_start", cxt.void_type().fn_type(&[], false), None);
                    {
                        let b = cxt.create_builder();
                        let bl = cxt.append_basic_block(new_fun, "entry");
                        b.position_at_end(bl);
                        if f.get_type().get_return_type().is_none() {
                            // CPS
                            // We need a tailcc stop function to pass as `main`'s continuation, as well as the start function
                            let any_ty = cxt
                                .i8_type()
                                .ptr_type(durin::inkwell::AddressSpace::Generic)
                                .as_basic_type_enum();
                            let fun2 = m.add_function(
                                "$_stop",
                                cxt.void_type().fn_type(&[any_ty, any_ty], false),
                                None,
                            );
                            fun2.set_call_conventions(durin::backend::TAILCC);
                            let fun_ty = fun2
                                .get_type()
                                .ptr_type(durin::inkwell::AddressSpace::Generic)
                                .as_basic_type_enum();
                            let clos_ty = cxt.struct_type(&[any_ty, fun_ty], false);
                            let clos = clos_ty.get_undef();
                            let clos = b
                                .build_insert_value(
                                    clos,
                                    fun2.as_global_value().as_pointer_value(),
                                    1,
                                    "_stop_clos",
                                )
                                .unwrap()
                                .as_basic_value_enum();

                            let unit = cxt
                                .struct_type(&[], false)
                                .get_undef()
                                .as_basic_value_enum();
                            let call = b.build_call(f, &[unit, clos], "main_call");
                            call.set_call_convention(durin::backend::TAILCC);
                            call.set_tail_call(true);
                            b.build_return(None);

                            let bl2 = cxt.append_basic_block(fun2, "entry");
                            b.position_at_end(bl2);
                            b.build_return(None);
                        } else {
                            // Direct style
                            let unit = cxt
                                .struct_type(&[], false)
                                .get_undef()
                                .as_basic_value_enum();
                            let call = b.build_call(f, &[unit], "main_call");
                            call.set_call_convention(durin::backend::TAILCC);
                            call.set_tail_call(true);
                            b.build_return(None);
                        }
                    }

                    // Then we JIT and run it
                    let ee = m
                        .create_jit_execution_engine(durin::inkwell::OptimizationLevel::None)
                        .expect("Failed to create LLVM execution engine");
                    if let Some(f) = m.get_function("malloc") {
                        ee.add_global_mapping(&f, malloc as usize);
                    }
                    if let Some(f) = m.get_function("print_i32") {
                        ee.add_global_mapping(&f, print_i32 as usize);
                    }
                    unsafe {
                        ee.run_function(new_fun, &[]);
                    }
                }
            }
            // `m` needs to be dropped before `cxt`
            drop(m);
        } else {
            db.write_errors();
            std::process::exit(1);
        }
    } else {
        repl::run_repl();
    }
}
