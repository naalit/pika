use std::io::Read;
use std::path::PathBuf;

use lsp_types::Url;
use ropey::Rope;

use crate::common::*;
use crate::elab::{DefBody, Definition, Elaborator};
use crate::parsing::Parser;
use crate::server::{DatabaseImpl, Server};

mod args;
mod common;
mod elab;
mod parsing;
mod pretty;
mod server;

use crate::args::*;

pub struct ElabResult {
    files: Vec<File>,
    db: DatabaseImpl,
}
pub struct ElabError {
    err: Error,
    split: SplitId,
    file: File,
}
impl ElabError {
    pub fn write_err(&self, result: &ElabResult) {
        let mut cache = FileCache::new(&result.db);
        self.err.clone().write_cli(
            &result.db.split_span(self.file, self.split).unwrap(),
            &mut cache,
        );
    }
}
impl ElabResult {
    pub fn all_errors(&self) -> Vec<ElabError> {
        self.files
            .iter()
            .copied()
            .flat_map(|file| {
                self.db
                    .all_errors(file)
                    .into_iter()
                    .map(move |(err, split)| ElabError { err, split, file })
            })
            .collect()
    }
}

pub fn elab_files(filenames: &[PathBuf]) -> Result<ElabResult, (PathBuf, std::io::Error)> {
    let mut files = Vec::new();
    let mut db = DatabaseImpl::default();
    for file_name in filenames {
        let file = std::fs::File::open(file_name).map_err(|e| (file_name.clone(), e))?;

        let buf = ropey::Rope::from_reader(file).unwrap();

        let file_id = db.file_id(FileLoc::Url(
            Url::from_file_path(file_name.canonicalize().unwrap()).unwrap(),
        ));
        db.set_input_file(file_id, buf);
        files.push(file_id);
    }

    Ok(ElabResult { files, db })
}

pub fn cli_main() {
    driver(Config::from_cmd_args())
}

pub fn driver(config: Config) {
    if config.command == Command::Server {
        let mut server = Server::start();
        server.main_loop();
        server.shutdown();
        return;
    } else if config.command == Command::Repl {
        let mut input = String::new();
        std::io::stdin().read_to_string(&mut input).unwrap();
        let input = Rope::from(input);
        let mut db = DatabaseImpl::default();
        let file = db.file_id(FileLoc::Input);
        db.set_input_file(file, input);

        let splits = db.all_split_ids(file);
        let mut cache = FileCache::new(&db);
        for split in splits {
            // let res = db.parse(file, split).unwrap();
            // let root = db.ast(file, split);
            // match root {
            //     Some(node) => {
            //         node.print_tree();
            //         node.pretty().emit_stderr()
            //     }
            //     None => eprintln!("<NO EXPRESSION>"),
            // }
            let def = db.def(DefLoc::Root(file, split));
            if let Some(def) = db.def_elab(def) {
                match def.result {
                    Some(Definition {
                        name,
                        ty,
                        body: DefBody::Let(body),
                        ..
                    }) => {
                        Doc::none()
                            .add("let", Doc::style_keyword())
                            .space()
                            .chain(name.pretty(&db))
                            .add(':', ())
                            .space()
                            .chain(ty.pretty(&db))
                            .space()
                            .add('=', ())
                            .space()
                            .chain(body.pretty(&db))
                            .emit_stderr();
                    }
                    Some(Definition {
                        name,
                        ty,
                        body: DefBody::Type(ctors),
                        ..
                    }) => {
                        Doc::none()
                            .add("type", Doc::style_keyword())
                            .space()
                            .chain(name.pretty(&db))
                            .add(':', ())
                            .space()
                            .chain(ty.pretty(&db))
                            .space()
                            .add("of", Doc::style_keyword())
                            .emit_stderr();
                        for (split, _, ty) in ctors {
                            Doc::none()
                                .add("  ", ())
                                .chain(split.name().map_or(Doc::start("??"), |x| x.pretty(&db)))
                                .add(':', ())
                                .space()
                                .chain(ty.quote(crate::elab::Size::zero(), None).pretty(&db))
                                .space()
                                .emit_stderr();
                        }
                    }
                    _ => todo!(),
                }
            }
        }
        for (e, split) in db.all_errors(file) {
            e.write_cli(&db.split_span(file, split).unwrap(), &mut cache);
        }

        return;
    }

    // CLI driver
    if config.files.is_empty() {
        Doc::none()
            .add("Error", ariadne::Color::Red.style())
            .add(": No input files: exiting", ())
            .emit_stderr();
        std::process::exit(1)
    }

    let ElabResult { files, db } = elab_files(&config.files).unwrap_or_else(|(file, _)| {
        Doc::none()
            .add("Error", ariadne::Color::Red)
            .add(": File not found: '", ())
            .add(file.display(), ariadne::Color::Cyan)
            .add("'", ())
            .emit_stderr();
        std::process::exit(1)
    });

    let mut cache = FileCache::new(&db);
    for file in files {
        if config.flag(Flag::ShowParseTree) {
            for split in db.all_split_ids(file) {
                if let Some(ast) = db.ast(file, split) {
                    ast.print_tree();
                }
            }
        }
        for (e, split) in db.all_errors(file) {
            e.write_cli(&db.split_span(file, split).unwrap(), &mut cache);
        }
    }
}
