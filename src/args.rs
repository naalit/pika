use std::collections::HashSet;
use std::{collections::VecDeque, path::PathBuf};

const HELP: &'static str = "Usage:
    pika [flags] command [files]

Commands:
    build       Compile files but don't run them
    run         Compile files and run the resulting executable
    check       Perform typechecking but don't compile to machine code

Flags:
    -h, --help  Show this help message
";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    Check,
    Build,
    Run,
}
impl Command {
    fn parse(s: &str) -> Option<Self> {
        match s {
            "check" => Some(Command::Check),
            "build" => Some(Command::Build),
            "run" => Some(Command::Run),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Flag {
    Help,
    EmitDurin,
    EmitLLVM,
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
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Opt {
    Output(PathBuf),
    OptLevel(u32),
}
impl Opt {
    fn short(c: char, val: &mut Option<String>) -> Option<Self> {
        match c {
            'o' => Some(Opt::Output(val.take().unwrap().into())),
            'O' => Some(Opt::OptLevel(
                val.take()
                    .unwrap()
                    .parse()
                    .expect("Expected number after -O"),
            )),
            _ => None,
        }
    }
    fn long(s: &str, val: &mut Option<String>) -> Option<Self> {
        match s {
            "output" => Some(Opt::Output(val.take().unwrap().into())),
            "opt-level" => Some(Opt::OptLevel(
                val.take()
                    .unwrap()
                    .parse()
                    .expect("Expected number after -O"),
            )),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Config {
    pub command: Command,
    pub files: Vec<PathBuf>,
    pub output: Option<PathBuf>,
    pub opt_level: u32,
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
        let mut opt_level = 0;
        for i in options {
            match i {
                Opt::Output(s) => output = Some(s),
                Opt::OptLevel(i) => opt_level = i,
            }
        }

        Config {
            command: command.unwrap_or(Command::Run),
            files,
            output,
            opt_level,
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
            } else if i.starts_with("-") {
                for (idx, c) in i.char_indices().skip(1) {
                    if let Some(flag) = Flag::short(c) {
                        args.flags.insert(flag);
                    } else {
                        if idx + 1 == i.len() {
                            let mut val = sargs.pop_front();
                            if let Some(opt) = Opt::short(c, &mut val) {
                                options.push(opt);
                            } else {
                                eprintln!("Unrecognized short flag '{}', ignoring; use '--flag' for long flags", c);
                                error = true;
                                sargs.push_front(val.unwrap());
                            }
                        } else if idx + 2 == i.len()
                            && i.chars().skip(idx + 1).next().unwrap().is_ascii_digit()
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
                            eprintln!("Unrecognized short flag '{}', ignoring; use '--flag' for long flags", c);
                            error = true;
                        }
                    }
                }
            } else if args.command.is_none() {
                if let Some(cmd) = Command::parse(&i) {
                    args.command = Some(cmd);
                } else {
                    eprintln!("Unrecognized command '{}', interpreting it as a file name and defaulting to 'check'; specify a command before input file names", i);
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
