mod bicheck;
mod binding;
mod codegen;
mod common;
mod elab;
mod error;
mod lexer;
mod options;
mod printing;
mod query;
mod repl;
mod term;
use lalrpop_util::lalrpop_mod;
lalrpop_mod!(pub grammar);

use crate::common::*;
use crate::error::FILES;
use crate::repl::*;
use arg::Args;
use std::fs::File;
use std::io::Read;
use std::time::Instant;

fn main() {
    // Skip the binary path
    let args: Vec<String> = std::env::args().skip(1).collect();
    match Options::from_args(args.iter().map(|x| &**x)) {
        Ok(options) => match options.command {
            Command::Repl => run_repl(&options),
            Command::Build | Command::Run => {
                let start_time = Instant::now();

                let mut db = MainDatabase::default();
                for i in &options.input_files {
                    let mut file = File::open(i).unwrap();
                    let mut buf = String::new();
                    file.read_to_string(&mut buf).expect("Error reading file");
                    if !buf.ends_with('\n') {
                        buf.push('\n');
                    }

                    let file = FILES
                        .write()
                        .unwrap()
                        .add("<input>".to_string(), buf.clone());
                    db.set_source(file, std::sync::Arc::new(buf));

                    let module = db.low_mod(file);

                    if db.has_errors() {
                        db.emit_errors();
                        std::process::exit(1)
                    } else {
                        eprintln!("Build successful in {:?}", Instant::now() - start_time);
                    }

                    if options.command == Command::Run || options.show_llvm {
                        // Generate LLVM and print out the module, for now
                        let context = inkwell::context::Context::create();
                        let llvm = module.codegen(&mut crate::codegen::CodegenCtx::new(&context));

                        if options.show_llvm {
                            llvm.print_to_stderr();
                        }

                        // For now we verify it but don't run it
                        if let Err(e) = llvm.verify() {
                            eprintln!("Verification error: {}", e);
                            std::process::exit(1);
                        } else if options.command == Command::Run {
                            let main_raw = db.bindings().write().unwrap().raw("main".to_string());
                            if let Some(main) = db
                                .symbols(ScopeId::File(file))
                                .iter()
                                .find(|x| x.raw() == main_raw)
                            {
                                let main_mangled = db.mangle(ScopeId::File(file), **main).unwrap();
                                let engine = llvm
                                    .create_jit_execution_engine(inkwell::OptimizationLevel::None)
                                    .expect("Failed to create LLVM execution engine");

                                use crate::elab::Elab;
                                use crate::term::Builtin;
                                match db
                                    .elab(ScopeId::File(file), **main)
                                    .unwrap()
                                    .get_type(&mut db.temp_env(ScopeId::File(file)))
                                {
                                    Elab::Builtin(Builtin::Int) => unsafe {
                                        let main_fun: inkwell::execution_engine::JitFunction<
                                            unsafe extern "C" fn() -> i32,
                                        > = engine.get_function(&main_mangled).unwrap();
                                        let result = main_fun.call();
                                        println!("{}", result);
                                    },
                                    Elab::Pair(x, y)
                                        if x == y && *x == Elab::Builtin(Builtin::Int) =>
                                    unsafe {
                                        // Rust aligns (i32, i32) differently than LLVM does, so values .1 and .3 in the result are padding
                                        let main_fun: inkwell::execution_engine::JitFunction<
                                            unsafe extern "C" fn() -> (i32, i32, i32, i32),
                                        > = engine.get_function(&main_mangled).unwrap();
                                        let result = main_fun.call();
                                        println!("({}, {})", result.0, result.2);
                                    }
                                    x => {
                                        eprintln!(
                                            "Error: Main can't return {}!",
                                            x.pretty(&*db.bindings().read().unwrap()).ansi_string()
                                        );
                                        std::process::exit(1)
                                    }
                                }
                            } else {
                                eprintln!("Run command specified but no `main` found!");
                                std::process::exit(1)
                            }
                        }
                    }
                }
            }
        },
        Err(err) => {
            eprintln!("{}", err);
            std::process::exit(1)
        }
    }
}
