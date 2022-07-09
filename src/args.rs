use std::collections::HashSet;
use std::{collections::VecDeque, path::PathBuf};

const HELP: &str = "Usage:
    pika [flags] command [files]

Commands:
    server              Start the Pika language server
    build               Compile files but don't run them
    run                 Compile files and run the resulting executable
    check               Perform typechecking but don't compile to machine code
    repl                Run the interactive Read-Evaluate-Print-Loop

Flags:
    -h, --help          Show this help message
    --release           Build in release mode with optimizations
    --emit-durin        Print out the Durin IR for the input files
    -o, --output PATH   Place the output binary at PATH
";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    Server,
    Check,
    Build,
    Run,
    Repl,
}
impl Command {
    fn parse(s: &str) -> Option<Self> {
        match s {
            "server" => Some(Command::Server),
            "check" => Some(Command::Check),
            "build" => Some(Command::Build),
            "run" => Some(Command::Run),
            "repl" => Some(Command::Repl),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Flag {
    Help,
    EmitDurin,
    EmitLLVM,
    Release,
    ShowParseTree,
}
impl Flag {
    fn short(c: char) -> Option<Self> {
        match c {
            'h' => Some(Flag::Help),
            _ => None,
        }
    }
    fn long(s: &str) -> Option<Self> {
        match s {
            "help" => Some(Flag::Help),
            "emit-durin" => Some(Flag::EmitDurin),
            "emit-llvm" => Some(Flag::EmitLLVM),
            "release" => Some(Flag::Release),
            "show-parse-tree" => Some(Flag::ShowParseTree),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Opt {
    Output(PathBuf),
}
impl Opt {
    fn short(c: char, val: &mut Option<String>) -> Option<Self> {
        match c {
            'o' => Some(Opt::Output(val.take().unwrap().into())),
            _ => None,
        }
    }
    fn long(s: &str, val: &mut Option<String>) -> Option<Self> {
        match s {
            "output" => Some(Opt::Output(val.take().unwrap().into())),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Config {
    pub command: Command,
    pub files: Vec<PathBuf>,
    pub output: Option<PathBuf>,
    pub flags: HashSet<Flag>,
}
impl Config {
    pub fn flag(&self, f: Flag) -> bool {
        self.flags.contains(&f)
    }

    fn new(args: Args, options: Vec<Opt>) -> Config {
        let Args {
            command,
            flags,
            files,
        } = args;

        let mut output = None;
        for i in options {
            match i {
                Opt::Output(s) => output = Some(s),
            }
        }

        Config {
            command: command.unwrap_or(Command::Repl),
            files,
            output,
            flags,
        }
    }

    pub fn from_cmd_args() -> Config {
        let mut args = Args::default();
        let mut options = Vec::new();
        let mut error = false;
        let mut sargs: VecDeque<_> = std::env::args().skip(1).collect();
        while let Some(i) = sargs.pop_front() {
            if i.starts_with("--") {
                if let Some(flag) = Flag::long(&i[2..]) {
                    args.flags.insert(flag);
                } else {
                    // Support both `--flag=val` and `--flag val`
                    if let Some(eq_idx) = i.find('=') {
                        let (i, val) = i.split_at(eq_idx);
                        let mut val = Some(val[1..].to_string());
                        if let Some(opt) = Opt::long(i, &mut val) {
                            options.push(opt);
                        } else {
                            eprintln!("Unrecognized option '{}', ignoring", i);
                            error = true;
                        }
                    } else {
                        let mut val = sargs.pop_front();
                        if let Some(opt) = Opt::long(&i, &mut val) {
                            options.push(opt);
                        } else {
                            eprintln!("Unrecognized option or flag '{}', ignoring", i);
                            error = true;
                            sargs.push_front(val.unwrap());
                        }
                    }
                }
            } else if i.starts_with('-') {
                for (idx, c) in i.char_indices().skip(1) {
                    if let Some(flag) = Flag::short(c) {
                        args.flags.insert(flag);
                    } else if idx + 1 == i.len() {
                        let mut val = sargs.pop_front();
                        if let Some(opt) = Opt::short(c, &mut val) {
                            options.push(opt);
                        } else {
                            eprintln!("Unrecognized short flag '{}', ignoring; use '--flag' for long flags", c);
                            error = true;
                            if let Some(val) = val {
                                sargs.push_front(val);
                            }
                        }
                    } else if idx + 2 == i.len() && i.chars().nth(idx + 1).unwrap().is_ascii_digit()
                    {
                        // Allow -O2 etc
                        let mut val = Some(i[idx + 1..].to_string());
                        if let Some(opt) = Opt::short(c, &mut val) {
                            options.push(opt);
                        } else {
                            eprintln!("Unrecognized short flag '{}', ignoring; use '--flag' for long flags", c);
                            error = true;
                        }
                        break;
                    } else {
                        eprintln!(
                            "Unrecognized short flag '{}', ignoring; use '--flag' for long flags",
                            c
                        );
                        error = true;
                    }
                }
            } else if args.command.is_none() {
                if let Some(cmd) = Command::parse(&i) {
                    args.command = Some(cmd);
                } else {
                    eprintln!("Unrecognized command '{}', interpreting it as a file name and defaulting to 'check'; specify a command before input file names", i);
                    args.command = Some(Command::Check);
                    args.files.push(i.into());
                    error = true;
                }
            } else {
                args.files.push(i.into());
            }
        }

        if args.flags.contains(&Flag::Help) {
            eprintln!("{}", HELP);
            std::process::exit(0);
        } else if error {
            eprintln!("Use -h or --help for help");
        }

        Config::new(args, options)
    }
}

#[derive(Default, Clone)]
struct Args {
    command: Option<Command>,
    flags: HashSet<Flag>,
    files: Vec<PathBuf>,
}
