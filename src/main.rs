use std::fs::File;
use std::io::Read;
use std::path::Path;

pub mod args;
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
use crate::args::{Command, Config, Flag};
use crate::pretty::{Doc, Style};
use crate::query::*;

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
    let config = Config::from_cmd_args();
    for file_name in &config.files {
        let mut file = File::open(file_name).unwrap_or_else(|_| {
            Doc::start("error")
                .style(Style::BoldRed)
                .add(": File not found: ")
                .add(file_name.display())
                .style(Style::Bold)
                .emit();
            std::process::exit(1)
        });

        let mut buf = String::new();
        file.read_to_string(&mut buf).unwrap();

        let mut db = Database::default();
        let file_id = error::FILES
            .write()
            .unwrap()
            .add(file_name.to_str().unwrap().to_string(), buf.clone());
        db.set_file_source(file_id, buf);
        db.check_all(file_id);

        if db.num_errors() == 0 {
            Doc::start("File elaborated successfully!")
                .style(Style::Bold)
                .emit();

            if matches!(config.command, Command::Build | Command::Run) {
                let mut durin = crate::lower::durin(&db, file_id);
                if config.flag(Flag::EmitDurin) {
                    eprintln!("{}", durin.emit());
                }

                let out_file = config.output.clone().unwrap_or_else(|| {
                    Path::new("target/debug/pika_out").join(file_name.file_stem().unwrap())
                });
                if let Some(parent) = out_file.parent() {
                    std::fs::create_dir_all(parent).unwrap();
                }
                if let Err(e) = durin.compile_and_link(&out_file) {
                    Doc::start("error")
                        .style(Style::BoldRed)
                        .add(": Compilation error: ")
                        .style(Style::Bold)
                        .add(e)
                        .emit();
                    std::process::exit(1);
                } else {
                    Doc::start("Compiled successfully!")
                        .style(Style::Bold)
                        .emit();
                }

                if matches!(config.command, Command::Run) {
                    if let Ok(out_file) = out_file.canonicalize() {
                        Doc::start("Running ")
                            .add(out_file.display())
                            .style(Style::Bold)
                            .emit();
                        std::process::Command::new(out_file).status().unwrap();
                    } else {
                        Doc::start("error")
                            .style(Style::BoldRed)
                            .add(": `run` command specified but module no executable present")
                            .style(Style::Bold)
                            .emit();
                        std::process::exit(1);
                    }
                }
            }
        } else {
            let num_errors = db.num_errors();
            db.write_errors();
            Doc::start("Exiting because of ")
                .add(num_errors)
                .add(" errors")
                .style(Style::Special)
                .emit();
            std::process::exit(1);
        }
    }
}
