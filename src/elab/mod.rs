use crate::{common::*, intern_key};

mod cxt;
mod elaborate;
pub mod ide_support;
mod metas;
mod pattern;
mod term;
mod unify;
mod val;
mod var;

use cxt::*;
use metas::*;
pub use term::*;
use val::*;
pub use var::*;

use self::unify::CheckReason;

#[salsa::query_group(ElabDatabase)]
pub trait Elaborator: crate::parsing::Parser {
    #[salsa::interned]
    fn def(&self, loc: DefLoc) -> Def;

    #[salsa::interned]
    fn def_node(&self, node: (ast::Def, DefCxt)) -> DefNode;

    #[salsa::interned]
    fn cons_id(&self, def: Def, cons: SplitId) -> Cons;

    fn root_defs_n(&self, file: File) -> Vec<(SplitId, DefNode)>;

    fn def_type_n(&self, def_id: Def, def_node: DefNode) -> DefTypeResult;

    fn def_elab_n(&self, def_id: Def, def_node: DefNode) -> DefElabResult;

    fn def_elab(&self, def: Def) -> Option<DefElabResult>;

    fn def_type(&self, def: Def) -> Option<DefTypeResult>;

    fn to_def_node(&self, def: Def) -> Option<DefNode>;

    fn def_name(&self, def: Def) -> Option<Name>;

    fn all_errors(&self, file: File) -> Vec<(Error, SplitId)>;
}

fn all_errors(db: &dyn Elaborator, file: File) -> Vec<(Error, SplitId)> {
    fn def_errors(
        db: &dyn Elaborator,
        def: Def,
        root: SplitId,
        errors: &mut Vec<(Error, SplitId)>,
    ) {
        if let Some(res) = db.def_type(def) {
            errors.extend(res.errors.into_iter().map(|x| (x, root)));
        }
        if let Some(res) = db.def_elab(def) {
            errors.extend(res.errors.into_iter().map(|x| (x, root)));
            for (split, _) in res.result.map(|x| x.children).unwrap_or_default() {
                def_errors(db, db.def(DefLoc::Child(def, split)), root, errors)
            }
        }
    }

    let splits = db.all_split_ids(file);
    let mut errors = Vec::new();
    for split in splits {
        if let Some(res) = db.parse(file, split) {
            errors.extend(res.errors.into_iter().map(|x| (x, split)));
        }
        let def = db.def(DefLoc::Root(file, split));
        def_errors(db, def, split, &mut errors)
    }
    errors
}

fn def_file(db: &dyn Elaborator, def: Def) -> File {
    match db.lookup_def(def) {
        DefLoc::Root(file, _) => file,
        DefLoc::Child(def, _) => def_file(db, def),
    }
}

fn def_name(db: &dyn Elaborator, def: Def) -> Option<Name> {
    match db.lookup_def(def) {
        DefLoc::Root(_, SplitId::Named(name)) => Some(name),
        DefLoc::Child(_, SplitId::Named(name)) => Some(name),
        _ => {
            let def_node = db.to_def_node(def)?;
            let (adef, _) = db.lookup_def_node(def_node);
            adef.name(db).map(|(n, _)| n)
        }
    }
}

fn root_defs_n(db: &dyn Elaborator, file: File) -> Vec<(SplitId, DefNode)> {
    db.all_split_ids(file)
        .into_iter()
        .filter_map(|split| {
            let def = db.ast(file, split)?.def()?;
            let node = db.def_node((def, DefCxt::global(file)));
            Some((split, node))
        })
        .collect()
}

fn to_def_node(db: &dyn Elaborator, def: Def) -> Option<DefNode> {
    match db.lookup_def(def) {
        DefLoc::Root(file, split) => db
            .root_defs_n(file)
            .into_iter()
            .find(|(x, _)| *x == split)
            .map(|(_, x)| x),
        DefLoc::Child(parent, split) => {
            // We have to completely elaborate the parent to find the type of the child
            // which makes sense since we need all the type information in the body to determine the context for the child
            let parent = db.def_elab(parent)?.result?;
            parent
                .children
                .into_iter()
                .find(|(x, _)| *x == split)
                .map(|(_, x)| x)
        }
    }
}

fn def_type_n(db: &dyn Elaborator, def_id: Def, def_node: DefNode) -> DefTypeResult {
    let (def, cxt) = db.lookup_def_node(def_node);
    let mut cxt = Cxt::new(db, cxt);
    let result = def.elab_type(def_id, def_node, &mut cxt);
    DefTypeResult {
        result,
        errors: cxt.emit_errors(),
    }
}

fn def_type(db: &dyn Elaborator, def: Def) -> Option<DefTypeResult> {
    db.to_def_node(def).map(|x| db.def_type_n(def, x))
}

fn def_elab_n(db: &dyn Elaborator, def_id: Def, def_node: DefNode) -> DefElabResult {
    let (def, cxt) = db.lookup_def_node(def_node);
    let mut cxt = Cxt::new(db, cxt);
    let result = def.elab(def_id, def_node, &mut cxt);
    DefElabResult {
        result,
        errors: cxt.emit_errors(),
    }
}

fn def_elab(db: &dyn Elaborator, def: Def) -> Option<DefElabResult> {
    db.to_def_node(def).map(|x| db.def_elab_n(def, x))
}

pub enum TypeError {
    NotFound(Name),
    Unify(unify::UnifyError),
    NotFunction(Expr, RelSpan),
    InvalidPattern(String, Expr),
    Other(Doc),
}
impl<T: Into<Doc>> From<T> for TypeError {
    fn from(x: T) -> Self {
        TypeError::Other(x.into())
    }
}
impl TypeError {
    fn to_error(&self, severity: Severity, mut span: RelSpan, db: &dyn Elaborator) -> Error {
        let (msg, label, note) = match self {
            TypeError::NotFound(name) => (
                Doc::start("Name not found: ").add(db.lookup_name(*name), Doc::COLOR1),
                Doc::start("This name not found"),
                None,
            ),
            TypeError::Unify(e) => return e.to_error(span, db),
            TypeError::Other(msg) => (msg.clone(), msg.clone(), None),
            TypeError::InvalidPattern(msg, ty) => (
                Doc::start("Invalid pattern: ")
                    .add(msg, ())
                    .chain(ty.pretty(db)),
                Doc::start(msg),
                None,
            ),
            TypeError::NotFunction(ty, fspan) => {
                span = *fspan;
                (
                    Doc::start("Expected function type in application, got '")
                        .chain(ty.pretty(db))
                        .add("'", ()),
                    Doc::start("This has type '")
                        .chain(ty.pretty(db))
                        .add("'", ()),
                    None,
                )
            }
        };
        Error {
            severity,
            message: msg,
            message_lsp: None,
            primary: Label {
                span,
                message: label,
                color: Some(Doc::COLOR1),
            },
            secondary: Vec::new(),
            note,
        }
    }
}
impl From<unify::UnifyError> for TypeError {
    fn from(x: unify::UnifyError) -> Self {
        TypeError::Unify(x)
    }
}

// Problem: we want things to look up definitions by location
// but with a design like this we can't use the child definitions within the body of the parent
// the worst-case is something like
//   let x = do
//     let y: Type = I32
//     fun f (): y = 12
//     let z = f ()
//     fun g () = z
// where def g depends on local z, local z depends on def f, and def f depends on local y
// this is probably impossible to do in a nice way
// alternative A:
// - eval has a check for not trying to inline defs that are children of this one
// - we elaborate types for child definitions within the parent
// - we never need to look inside child definitions
// alternative B:
// - still not allowed to inline children
// - intern a (ast::Def, DefCxt) pair to e.g. DefNode
// - elaborate def query takes a DefNode, returns list of child DefNodes
// - another query that takes a Def and calls the above
// - elaborating types occurs in salsa
// alternative B is the same as A except type elaboration isn't duplicated so it's just better
intern_key!(DefNode);
intern_key!(Cons);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefElabResult {
    pub result: Option<Definition>,
    pub errors: Vec<Error>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefTypeResult {
    result: Option<Val>,
    errors: Vec<Error>,
}

enum NumLiteral {
    IPositive(u64),
    INegative(i64),
    Float(f64),
}
fn lex_number(s: &str) -> Result<NumLiteral, String> {
    let mut chars = s.chars().peekable();
    let mut buf = String::new();
    let neg = chars.peek() == Some(&'-');
    if neg {
        buf.push(chars.next().unwrap());
    }
    let mut base = 10;
    if chars.peek() == Some(&'0') {
        buf.push(chars.next().unwrap());
        match chars.peek() {
            Some('x') => {
                chars.next();
                base = 16;
            }
            Some('b') => {
                chars.next();
                base = 2;
            }
            _ => (),
        }
    }
    let mut float = false;
    while let Some(&next) = chars.peek() {
        if next.is_digit(base) {
            buf.push(next);
            chars.next();
        } else if next == '_' {
            chars.next();
        } else if next.is_alphanumeric() {
            chars.next();
            if base != 10 {
                return Err(format!(
                    "Invalid digit for base {} int literal: {}",
                    base, next
                ));
            } else {
                return Err(format!("Invalid digit for int literal: {}", next));
            }
        } else if next == '.' {
            float = true;
            buf.push(next);
            chars.next();
        } else {
            break;
        }
    }
    use std::str::FromStr;
    if float {
        match f64::from_str(&buf) {
            Ok(f) => Ok(NumLiteral::Float(f)),
            Err(e) => {
                return Err(e.to_string());
            }
        }
    } else if neg {
        match i64::from_str_radix(&buf, base) {
            Ok(i) => Ok(NumLiteral::INegative(i)),
            // TODO when `ParseIntError::kind()` gets stabilized (or Pika switches to nightly Rust) make custom error messages
            Err(e) => {
                return Err(e.to_string());
            }
        }
    } else {
        match u64::from_str_radix(&buf, base) {
            Ok(i) => Ok(NumLiteral::IPositive(i)),
            // TODO when `ParseIntError::kind()` gets stabilized (or Pika switches to nightly Rust) make custom error messages
            Err(e) => {
                return Err(e.to_string());
            }
        }
    }
}
