use std::collections::HashMap;
use std::error::Error;
use std::io::Read;

use common::ast::{AstNode, Pretty};
use lsp_types::notification::{Notification, PublishDiagnostics};
use lsp_types::request::GotoDefinition;
use lsp_types::request::Request;
use lsp_types::*;

use lsp_server as lsp;
use parsing::{Parser, ParserDatabase};
use ropey::Rope;

mod args;
pub mod common;
mod parsing;
pub mod pretty;
use common::*;

use crate::parsing::SyntaxNode;

#[salsa::database(ParserDatabase)]
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
            GotoDefinition::METHOD => {
                eprintln!("Handling GoToDefinition");
                let (id, params): (_, GotoDefinitionParams) =
                    msg.extract(GotoDefinition::METHOD)?.1;
                // example go to definition handler
                let result = Some(GotoDefinitionResponse::Array(Vec::new()));
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
            let splits = self.db.all_splits(file);
            let mut diagnostics = Vec::new();
            for split in splits {
                let mut lexer = parsing::lexer::Lexer::new(split.text.slice(..));
                let lex = lexer.lex();
                for (e, span) in lex.error {
                    let e = parsing::lexer::lexerror_to_error(e, span);
                    let e = e.to_lsp(&split.abs_span, &self.source, &self.db);
                    diagnostics.push(e);
                }
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

fn print_tree(node: &SyntaxNode, indent: usize) {
    for _ in 0..indent {
        print!(" ");
    }
    println!("{:?}", node);
    for i in node.children_with_tokens() {
        match i {
            rowan::NodeOrToken::Node(n) => print_tree(&n, indent + 2),
            rowan::NodeOrToken::Token(t) => {
                for _ in 0..indent + 2 {
                    print!(" ");
                }
                println!("{:?}", t);
            }
        }
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
            let res = crate::parsing::parser::parser_entry(&db, file, split).unwrap();
            let node = SyntaxNode::new_root(res.green);
            print_tree(&node, 0);
            let node = ast::Root::cast(node);
            match node {
                Some(node) => node.pretty().emit_stderr(),
                None => eprintln!("<NO EXPRESSION>"),
            }
            for e in res.errors {
                e.write_cli(&db.split(file, split).unwrap().abs_span, &mut cache);
            }
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

        let file_id = db.file_id(FileLoc::Url(Url::from_file_path(file_name).unwrap()));
        db.set_input_file(file_id, buf);
        files.push(file_id);
    }

    let mut cache = FileCache::new(&db);
    for file in files {
        let splits = db.all_splits(file);
        for split in splits {
            let mut lexer = parsing::lexer::Lexer::new(split.text.slice(..));
            let lex = lexer.lex();
            for (e, span) in lex.error {
                let e = parsing::lexer::lexerror_to_error(e, span);
                e.write_cli(&split.abs_span, &mut cache);
            }
        }
    }
}
