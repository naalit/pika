"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.deactivate = exports.activate = void 0;
const path = require("path");
const vscode_1 = require("vscode");
const node_1 = require("vscode-languageclient/node");
let client;
function activate(context) {
    // The server is implemented in node
    let serverModule = context.asAbsolutePath(path.join('..', '..', 'target', 'debug', 'pika2'));
    // If the extension is launched in debug mode then the debug server options are used
    // Otherwise the run options are used
    let serverOptions = {
        run: {
            command: serverModule,
            args: ["server"],
            options: {}
        },
        debug: {
            command: serverModule,
            args: ["server"],
            options: {}
        }
    };
    // Options to control the language client
    let clientOptions = {
        // Register the server for Pika files
        documentSelector: [{ scheme: 'file', language: 'pika' }],
        synchronize: {
            // Notify the server about file changes to '.clientrc files contained in the workspace
            fileEvents: vscode_1.workspace.createFileSystemWatcher('**/.clientrc')
        }
    };
    // Create the language client and start the client.
    client = new node_1.LanguageClient('pikaLanguageServer', 'Pika Language Server', serverOptions, clientOptions);
    // Start the client. This will also launch the server
    client.start();
}
exports.activate = activate;
function deactivate() {
    if (!client) {
        return undefined;
    }
    return client.stop();
}
exports.deactivate = deactivate;
//# sourceMappingURL=extension.js.map