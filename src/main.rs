use std::collections::HashMap;
use std::error::Error;
use std::io::Read;

use lsp_server as lsp;
use lsp_types::notification::{Notification, PublishDiagnostics};
use lsp_types::request::GotoDefinition;
use lsp_types::request::Request;
use lsp_types::*;
use ropey::Rope;

mod args;
mod common;
mod elab;
mod parsing;
mod pretty;

use crate::elab::{DefBody, Definition, ElabDatabase, Elaborator};
use crate::parsing::{Parser, ParserDatabase, ParserExt};
use common::*;

#[salsa::database(ParserDatabase, ElabDatabase)]
#[derive(Default)]
pub struct DatabaseImpl {
    storage: salsa::Storage<DatabaseImpl>,
}
impl salsa::Database for DatabaseImpl {}

pub struct Server {
    io_threads: lsp::IoThreads,
    connection: lsp::Connection,
    initialization_params: InitializeParams,
    source: HashMap<File, Rope>,
    db: DatabaseImpl,
}
impl Server {
    fn start() -> Self {
        // Note that  we must have our logging only write out to stderr.
        eprintln!("starting generic LSP server");

        // Create the transport. Includes the stdio (stdin and stdout) versions but this could
        // also be implemented to use sockets or HTTP.
        let (connection, io_threads) = lsp::Connection::stdio();

        // Run the server and wait for the two threads to end (typically by trigger LSP Exit event).
        let server_capabilities = serde_json::to_value(&ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(
                TextDocumentSyncKind::INCREMENTAL,
            )),
            definition_provider: Some(OneOf::Left(true)),
            hover_provider: Some(HoverProviderCapability::Simple(true)),
            ..Default::default()
        })
        .unwrap();
        let initialization_params = connection.initialize(server_capabilities).unwrap();
        let initialization_params: InitializeParams =
            serde_json::from_value(initialization_params).unwrap();

        Server {
            source: HashMap::new(),
            io_threads,
            connection,
            initialization_params,
            db: DatabaseImpl::default(),
        }
    }

    fn shutdown(self) {
        self.io_threads.join().unwrap();
    }

    fn main_loop(&mut self) {
        while let Ok(msg) = self.connection.receiver.recv() {
            eprintln!("Got message!");
            match msg {
                lsp::Message::Request(msg) => self.handle_request(msg),
                lsp::Message::Response(msg) => self.handle_response(msg),
                lsp::Message::Notification(msg) => self.handle_notification(msg),
            }
            .unwrap_or_else(|e| {
                eprintln!("WARNING: error in handling message: {}", e);
            })
        }
    }

    fn handle_response(&mut self, msg: lsp::Response) -> Result<(), Box<dyn Error>> {
        eprintln!("Ignoring response");
        Ok(())
    }

    fn handle_request(&mut self, msg: lsp::Request) -> Result<(), Box<dyn Error>> {
        if self.connection.handle_shutdown(&msg).unwrap() {
            eprintln!("Shutdown request received");
            return Ok(());
        }

        match &*msg.method {
            request::HoverRequest::METHOD => {
                let (id, params): (_, lsp_types::HoverParams) =
                    msg.extract(request::HoverRequest::METHOD)?;
                let file = self.db.file_id(FileLoc::Url(
                    params.text_document_position_params.text_document.uri,
                ));
                let pos = params.text_document_position_params.position;
                let source = self.source.get(&file).unwrap();
                let pos = source
                    .char_to_byte(source.line_to_char(pos.line as usize) + pos.character as usize)
                    as u32;
                if let Some(split) = self.db.split_at(file, pos) {
                    let aspan = self.db.split_span(file, split).unwrap();
                    if let Some((ty, span)) = crate::elab::ide_support::hover_type(
                        &self.db,
                        file,
                        split,
                        pos - aspan.1.start,
                    ) {
                        let range = aspan.add(span).lsp_range(&self.source);
                        let result = Hover {
                            contents: HoverContents::Scalar(MarkedString::LanguageString(
                                LanguageString {
                                    language: "pika".into(),
                                    value: ty.to_string(false),
                                },
                            )),
                            range: Some(range),
                        };
                        let result = serde_json::to_value(&result)?;
                        let resp = lsp::Response {
                            id,
                            result: Some(result),
                            error: None,
                        };
                        self.connection.sender.send(lsp::Message::Response(resp))?;
                        return Ok(());
                    }
                }
                let resp = lsp::Response {
                    id,
                    result: Some(serde_json::Value::Null),
                    error: None,
                };
                self.connection.sender.send(lsp::Message::Response(resp))?;
            }
            GotoDefinition::METHOD => {
                eprintln!("Handling GoToDefinition");
                let (id, params): (_, GotoDefinitionParams) =
                    msg.extract(GotoDefinition::METHOD)?;
                // example go to definition handler
                let result = GotoDefinitionResponse::Array(Vec::new());
                let result = serde_json::to_value(&result)?;
                let resp = lsp::Response {
                    id,
                    result: Some(result),
                    error: None,
                };
                self.connection.sender.send(lsp::Message::Response(resp))?;
            }
            _ => eprintln!("Ignored unknown request {}", msg.method),
        }

        Ok(())
    }

    fn handle_notification(&mut self, msg: lsp::Notification) -> Result<(), Box<dyn Error>> {
        use lsp_types::notification::*;
        match &*msg.method {
            DidOpenTextDocument::METHOD => {
                eprintln!("Received DidOpenTextDocument");
                let params: DidOpenTextDocumentParams = msg.extract(DidOpenTextDocument::METHOD)?;
                let file = params.text_document.uri;
                let file = self.db.file_id(FileLoc::Url(file));
                let source = params.text_document.text.into();
                self.source.insert(file, source);
                self.signal_change();
            }
            DidChangeTextDocument::METHOD => {
                eprintln!("Received DidChangeTextDocument");
                let params: DidChangeTextDocumentParams =
                    msg.extract(DidChangeTextDocument::METHOD)?;
                let file = params.text_document.uri;
                let file = self.db.file_id(FileLoc::Url(file));
                let source = self.source.get_mut(&file).unwrap();
                for change in params.content_changes {
                    if let Some(range) = change.range {
                        let start = source.line_to_char(range.start.line as usize)
                            + range.start.character as usize;
                        let end = source.line_to_char(range.end.line as usize)
                            + range.end.character as usize;
                        source.remove(start..end);
                        source.insert(start, &change.text);
                    } else {
                        // If range is None then it's the whole document
                        *source = Rope::from(change.text);
                    }
                }
                self.signal_change();
            }
            _ => eprintln!("Ignored unknown notification {}", msg.method),
        }

        Ok(())
    }

    fn signal_change(&mut self) {
        // Publish diagnostics (example)
        eprintln!("Starting diagnostic publishing...");
        for (&file, source) in &self.source {
            self.db.set_input_file(file, source.clone());
            let mut diagnostics = Vec::new();
            for (e, split) in self.db.all_errors(file) {
                let e = e.to_lsp(
                    &self.db.split_span(file, split).unwrap(),
                    &self.source,
                    &self.db,
                );
                diagnostics.push(e);
            }
            // TODO only send diagnostics if they changed
            let message = lsp::Notification {
                method: PublishDiagnostics::METHOD.to_string(),
                params: serde_json::to_value(&PublishDiagnosticsParams {
                    uri: self.db.lookup_file_id(file).to_url().unwrap(),
                    version: None,
                    diagnostics,
                })
                .unwrap(),
            };
            self.connection
                .sender
                .send(lsp::Message::Notification(message))
                .unwrap();
        }
        eprintln!("Published diagnostics!");
    }
}

fn main() {
    use args::*;

    let config = Config::from_cmd_args();
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
                        body: DefBody::Type(_ctors),
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
                            .add('=', ())
                            .space()
                            .add("...", ())
                            .emit_stderr();
                    }
                    None => todo!(),
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

    let mut files = Vec::new();
    let mut db = DatabaseImpl::default();
    for file_name in &config.files {
        let file = std::fs::File::open(file_name).unwrap_or_else(|_| {
            Doc::none()
                .add("Error", ariadne::Color::Red)
                .add(": File not found: '", ())
                .add(file_name.display(), ariadne::Color::Cyan)
                .add("'", ())
                .emit_stderr();
            std::process::exit(1)
        });

        let buf = ropey::Rope::from_reader(file).unwrap();

        let file_id = db.file_id(FileLoc::Url(
            Url::from_file_path(file_name.canonicalize().unwrap()).unwrap(),
        ));
        db.set_input_file(file_id, buf);
        files.push(file_id);
    }

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
