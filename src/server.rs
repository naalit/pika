use std::collections::HashMap;
use std::error::Error;

use lsp_server as lsp;
use lsp_types::notification::{Notification, PublishDiagnostics};
use lsp_types::request::GotoDefinition;
use lsp_types::request::Request;
use lsp_types::*;
use ropey::Rope;

use crate::common::*;
use crate::elab::{ElabDatabase, Elaborator};
use crate::parsing::{Parser, ParserDatabase, ParserExt};

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
    pub fn start() -> Self {
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

    pub fn shutdown(self) {
        self.io_threads.join().unwrap();
    }

    pub fn main_loop(&mut self) {
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
