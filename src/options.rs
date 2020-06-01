use arg::Args;

#[derive(Args, Debug)]
///Pika compiler
///Provide no input files for REPL mode
pub struct Options {
    #[arg(long)]
    ///Should the REPL generate LLVM code and print it to stderr?
    pub show_llvm: bool,

    ///The files to compile
    pub input_files: Vec<String>,
}
