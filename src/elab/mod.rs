use crate::{common::*, intern_key, parsing::ast::Pretty};

mod metas;
mod pattern;
mod term;
mod unify;
mod val;
mod var;

use metas::*;
pub use term::*;
use val::*;
use var::*;

#[salsa::query_group(ElabDatabase)]
pub trait Elaborator: crate::parsing::Parser {
    #[salsa::interned]
    fn def(&self, loc: DefLoc) -> Def;

    #[salsa::interned]
    fn def_node(&self, node: (ast::Def, DefCxt)) -> DefNode;

    fn root_defs_n(&self, file: File) -> Vec<(SplitId, DefNode)>;

    fn def_type_n(&self, def: DefNode) -> DefTypeResult;

    fn def_elab_n(&self, def: DefNode) -> DefElabResult;

    fn def_elab(&self, def: Def) -> Option<DefElabResult>;

    fn def_type(&self, def: Def) -> Option<DefTypeResult>;

    fn to_def_node(&self, def: Def) -> Option<DefNode>;

    fn def_name(&self, def: Def) -> Option<Name>;
}

fn def_name(db: &dyn Elaborator, def: Def) -> Option<Name> {
    match db.lookup_def(def) {
        DefLoc::Root(_, SplitId::Named(name)) => Some(name),
        DefLoc::Child(_, SplitId::Named(name)) => Some(name),
        _ => {
            let def_node = db.to_def_node(def)?;
            let (def, _) = db.lookup_def_node(def_node);
            match def {
                ast::Def::LetDef(x) => x.pat()?.expr()?.as_let_def_pat(&mut Cxt::new(db, DefCxt::global())).0,
                ast::Def::FunDef(x) => Some(x.name()?.name(db)),
                ast::Def::TypeDef(x) => Some(x.name()?.name(db)),
                ast::Def::TypeDefShort(x) => Some(x.name()?.name(db)),
                ast::Def::TypeDefStruct(x) => Some(x.name()?.name(db)),
            }
        }
    }
}

fn root_defs_n(db: &dyn Elaborator, file: File) -> Vec<(SplitId, DefNode)> {
    db.all_split_ids(file)
        .into_iter()
        .filter_map(|split| {
            let def = db.ast(file, split)?.def()?;
            let node = db.def_node((def, DefCxt::global()));
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
        DefLoc::Child(parent, _) => {
            // We have to completely elaborate the parent to find the type of the child
            // which makes sense since we need all the type information in the body to determine the context for the child
            let parent = db.def_elab(parent)?;
            parent
                .children
                .into_iter()
                .find(|(x, _)| *x == def)
                .map(|(_, x)| x)
        }
    }
}

fn def_type_n(db: &dyn Elaborator, def_node: DefNode) -> DefTypeResult {
    let (def, cxt) = db.lookup_def_node(def_node);
    let mut cxt = Cxt::from_def_cxt(db, cxt);
    let result = def.elab_type(def_node, &mut cxt);
    DefTypeResult {
        result,
        errors: cxt.emit_errors(),
    }
}

fn def_type(db: &dyn Elaborator, def: Def) -> Option<DefTypeResult> {
    db.to_def_node(def).map(|x| db.def_type_n(x))
}

fn def_elab_n(db: &dyn Elaborator, def_node: DefNode) -> DefElabResult {
    let (def, cxt) = db.lookup_def_node(def_node);
    let mut cxt = Cxt::from_def_cxt(db, cxt);
    let result = def.elab(def_node, &mut cxt);
    DefElabResult {
        result,
        errors: cxt.emit_errors(),
        // TODO def children
        children: Vec::new(),
    }
}

fn def_elab(db: &dyn Elaborator, def: Def) -> Option<DefElabResult> {
    db.to_def_node(def).map(|x| db.def_elab_n(x))
}

enum TypeError {
    NotFound(Name),
    Unify(Expr, Expr),
    Other(String),
}
impl TypeError {
    fn to_error(&self, span: RelSpan, db: &dyn Elaborator) -> Error {
        let mut gen = ariadne::ColorGenerator::new();
        let ca = gen.next();
        let (msg, label, note) = match self {
            TypeError::NotFound(name) => (
                Doc::start("Name not found: ")
                    .add(db.lookup_name(*name), ca),
                Doc::start("This name not found"),
                None,
            ),
            TypeError::Unify(a, b) => todo!("pretty print Expr"),
            TypeError::Other(msg) => (Doc::start(&msg), Doc::start(&msg), None),
        };
        Error {
            severity: Severity::Error,
            message: msg,
            primary: Label {
                span,
                message: label,
                color: Some(ca),
            },
            secondary: Vec::new(),
            note,
        }
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefElabResult {
    result: Option<Definition>,
    errors: Vec<Error>,
    children: Vec<(Def, DefNode)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefTypeResult {
    result: Option<Val>,
    errors: Vec<Error>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DefCxt {
    scopes: Vec<ScopeState>,
}
impl DefCxt {
    fn global() -> Self {
        DefCxt {
            scopes: vec![Scope::global().state()],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ScopeState {
    global: bool,
    size: Size,
    names: Vec<(Name, (Var<Lvl>, Val))>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Scope {
    global: bool,
    size: Size,
    names: HashMap<Name, (Var<Lvl>, Val)>,
}
impl Scope {
    fn state(&self) -> ScopeState {
        ScopeState {
            global: self.global,
            size: self.size,
            names: self
                .names
                .iter()
                .map(|(a, b)| (a.clone(), b.clone()))
                .collect(),
        }
    }

    fn from_state(state: ScopeState) -> Scope {
        Scope {
            global: state.global,
            size: state.size,
            names: HashMap::from_iter(state.names),
        }
    }

    fn define(&mut self, name: Name, var: Var<Lvl>, ty: Val) {
        self.names.insert(name, (var, ty));
    }

    fn define_local(&mut self, name: Name, ty: Val) {
        self.define(name, Var::Local(name, self.size.next_lvl()), ty);
        self.size = self.size.inc();
    }

    fn global() -> Self {
        Scope {
            global: true,
            size: Size::zero(),
            names: HashMap::new(),
        }
    }

    fn new(size: Size) -> Self {
        Scope {
            global: false,
            size,
            names: HashMap::new(),
        }
    }
}

struct Cxt<'a> {
    db: &'a dyn Elaborator,
    scopes: Vec<Scope>,
    errors: Vec<Spanned<TypeError>>,
}
impl Cxt<'_> {
    fn new(db: &dyn Elaborator, def_cxt: DefCxt) -> Cxt {
        Cxt {
            db,
            scopes: def_cxt.scopes.into_iter().map(Scope::from_state).collect(),
            errors: Vec::new(),
        }
    }

    fn from_def_cxt(db: &dyn Elaborator, def_cxt: DefCxt) -> Cxt {
        Cxt {
            db,
            scopes: def_cxt.scopes.into_iter().map(Scope::from_state).collect(),
            errors: Vec::new(),
        }
    }

    fn def_cxt(&self) -> DefCxt {
        DefCxt {
            scopes: self.scopes.iter().map(Scope::state).collect(),
        }
    }

    fn emit_errors(&self) -> Vec<Error> {
        self.errors
            .iter()
            .map(|(x, span)| x.to_error(span.clone(), self.db))
            .collect()
    }

    fn size(&self) -> Size {
        self.scopes.last().unwrap().size
    }

    fn scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    fn scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    fn push(&mut self) {
        self.scopes.push(Scope::new(self.size()));
    }

    fn pop(&mut self) {
        self.scopes.pop();
    }

    fn lookup(&self, name: Name) -> Option<(Var<Lvl>, Val)> {
        self.scopes
            .iter()
            .rev()
            .find_map(|x| x.names.get(&name).cloned())
    }

    fn error(&mut self, span: RelSpan, error: TypeError) {
        self.errors.push((error, span));
    }
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
            return Err(format!("Invalid digit for int literal: {}", next));
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

impl ast::Expr {
    fn as_let_def_pat(&self, cxt: &mut Cxt) -> (Option<Name>, Option<ast::Ty>) {
        match self {
            ast::Expr::Var(n) => (Some(n.name(cxt.db)), None),
            ast::Expr::GroupedExpr(x) => x
                .expr()
                .map(|x| x.as_let_def_pat(cxt))
                .unwrap_or((None, None)),
            ast::Expr::Binder(x) => {
                let (name, ty) = x
                    .pat()
                    .and_then(|x| x.expr())
                    .map(|x| x.as_let_def_pat(cxt))
                    .unwrap_or((None, None));
                if ty.is_some() {
                    cxt.error(
                        x.pat().unwrap().span(),
                        TypeError::Other(
                            "Binder (_:_) is not allowed to be nested in another binder"
                                .to_string(),
                        ),
                    );
                }
                (name, x.ty())
            }
            ast::Expr::Hole(_) => (Some(cxt.db.name("_".to_string())), None),
            _ => (None, None),
        }
    }
}

impl ast::Def {
    fn elab_type(&self, def_node: DefNode, cxt: &mut Cxt) -> Option<Val> {
        match self {
            ast::Def::LetDef(l) => match l.pat()?.expr()?.as_let_def_pat(cxt) {
                (_, Some(ty)) => Some(
                    ty.expr()?
                        .check(Val::Type, cxt)
                        .eval(&mut Env::new(cxt.size())),
                ),
                _ => {
                    // Infer the type from the value if possible
                    let def = cxt.db.def_elab_n(def_node);
                    match def.result {
                        Some(Definition::Let { ty, .. }) => {
                            Some(ty.eval(&mut Env::new(cxt.size())))
                        }
                        _ => None,
                    }
                }
            },
            ast::Def::FunDef(_) => todo!(),
            ast::Def::TypeDef(_) => todo!(),
            ast::Def::TypeDefShort(_) => todo!(),
            ast::Def::TypeDefStruct(_) => todo!(),
        }
    }

    fn elab(&self, def_node: DefNode, cxt: &mut Cxt) -> Option<Definition> {
        match self {
            ast::Def::LetDef(x) => {
                let (name, ty) = x.pat()?.expr()?.as_let_def_pat(cxt);
                match (name, ty) {
                    (Some(name), None) => {
                        let (body, ty) = x.body()?.expr()?.infer(cxt);
                        Some(Definition::Let {
                            name,
                            ty: Box::new(ty.quote(cxt.size())),
                            body: Box::new(body),
                        })
                    }
                    (Some(name), Some(_ty)) => {
                        // We already elaborated the type, so avoid doing that twice
                        let ty = cxt.db.def_type_n(def_node).result?;
                        let body = x.body()?.expr()?.check(ty.clone(), cxt);
                        Some(Definition::Let {
                            name,
                            ty: Box::new(ty.quote(cxt.size())),
                            body: Box::new(body),
                        })
                    }
                    (None, _) => None,
                }
            }
            ast::Def::FunDef(_) => todo!(),
            ast::Def::TypeDef(_) => todo!(),
            ast::Def::TypeDefShort(_) => todo!(),
            ast::Def::TypeDefStruct(_) => todo!(),
        }
    }
}

impl ast::Lit {
    pub(self) fn to_literal(&self, cxt: &Cxt) -> Result<Literal, String> {
        if let Some(l) = self.string() {
            // Process escape sequences to get the string's actual contents
            // This work is also done by the lexer, which then throws it away;
            // TODO move all error checking here and simplify the lexer code (same for numbers)
            let mut buf = String::new();
            let mut chars = l.text().chars().skip_while(|x| x.is_whitespace());
            loop {
                match chars.next() {
                    Some('"') => break,
                    Some('\\') => {
                        // Escape
                        match chars.next() {
                            Some('\\') => {
                                buf.push('\\');
                            }
                            Some('n') => {
                                buf.push('\n');
                            }
                            Some('t') => {
                                buf.push('\t');
                            }
                            _ => {
                                panic!("Invalid escape should have been caught in lexer");
                            }
                        }
                    }
                    Some(c) => buf.push(c),
                    None => {
                        panic!("Unclosed string should have been caught in lexer")
                    }
                }
            }
            Ok(Literal::String(cxt.db.name(buf)))
        } else if let Some(l) = self.int().or(self.float()) {
            let num = lex_number(l.text()).map_err(|e| format!("invalid literal: {}", e))?;
            match num {
                NumLiteral::IPositive(_) => todo!(),
                NumLiteral::INegative(_) => todo!(),
                NumLiteral::Float(_) => todo!(),
            }
            todo!()
        } else {
            todo!("invalid literal: {:?}", self.syntax());
        }
    }
}

impl ast::Expr {
    fn check(&self, ty: Val, cxt: &mut Cxt) -> Expr {
        todo!()
    }

    fn infer(&self, cxt: &mut Cxt) -> (Expr, Val) {
        // TODO hopefully try {} blocks stabilize soon and this won't be necessary
        let mut result = || {
            Ok({
                match self {
                    ast::Expr::Var(name) => {
                        let name = name.name(cxt.db);
                        let (v, t) = cxt.lookup(name).ok_or(TypeError::NotFound(name))?;
                        (Expr::var(v.cvt(cxt.size())), t)
                    }
                    ast::Expr::Lam(_) => todo!(),
                    ast::Expr::Pi(_) => todo!(),
                    ast::Expr::App(_) => todo!(),
                    ast::Expr::Do(_) => todo!(),
                    ast::Expr::Hole(_) => todo!(),
                    ast::Expr::Case(case) => {
                        let mut rty = None;
                        let (scrutinee, case) = case.elaborate(&mut rty, cxt);
                        let rty = rty.unwrap();
                        (
                            Expr::Elim(Box::new(scrutinee), Box::new(Elim::Case(case))),
                            rty,
                        )
                    }
                    ast::Expr::Lit(l) => match l.to_literal(cxt) {
                        Ok(l) => (
                            Expr::Lit(l),
                            Val::var(Var::Builtin(match l {
                                Literal::Int(_) => todo!(),
                                Literal::F64(_) => todo!(),
                                Literal::F32(_) => todo!(),
                                Literal::String(_) => Builtin::StringType,
                            })),
                        ),
                        Err(e) => {
                            cxt.error(self.span(), TypeError::Other(e));
                            (Expr::Error, Val::Error)
                        }
                    },
                    ast::Expr::BinOp(x) => {
                        let tok = x
                            .op()
                            .ok_or_else(|| TypeError::Other(format!("missing operator")))?;
                        let tok = tok
                            .syntax()
                            .children_with_tokens()
                            .find_map(|x| x.as_token().map(|x| x.kind()).filter(|x| x.is_binop()))
                            .unwrap_or(crate::parsing::SyntaxKind::Error);

                        if let Some(op) = ArithOp::from_tok(tok) {
                            let (a, ty) = x
                                .a()
                                .ok_or_else(|| {
                                    TypeError::Other(format!(
                                        "missing left operand for operator {}",
                                        tok
                                    ))
                                })?
                                .infer(cxt);
                            let b = x
                                .b()
                                .ok_or_else(|| {
                                    TypeError::Other(format!(
                                        "missing right operand for operator {}",
                                        tok
                                    ))
                                })?
                                .check(ty.clone(), cxt);
                            (
                                Expr::Elim(
                                    Box::new(Expr::var(Var::Builtin(Builtin::ArithOp(op)))),
                                    Box::new(Elim::App(Args {
                                        implicit: None,
                                        explicit: Some(Box::new(Expr::Pair(
                                            Box::new(a),
                                            Box::new(b),
                                        ))),
                                    })),
                                ),
                                ty,
                            )
                        } else if let Some(op) = CompOp::from_tok(tok) {
                            let (a, ty) = x
                                .a()
                                .ok_or_else(|| {
                                    TypeError::Other(format!(
                                        "missing left operand for operator {}",
                                        tok
                                    ))
                                })?
                                .infer(cxt);
                            let b = x
                                .b()
                                .ok_or_else(|| {
                                    TypeError::Other(format!(
                                        "missing right operand for operator {}",
                                        tok
                                    ))
                                })?
                                .check(ty, cxt);
                            (
                                Expr::Elim(
                                    Box::new(Expr::var(Var::Builtin(Builtin::CompOp(op)))),
                                    Box::new(Elim::App(Args {
                                        implicit: None,
                                        explicit: Some(Box::new(Expr::Pair(
                                            Box::new(a),
                                            Box::new(b),
                                        ))),
                                    })),
                                ),
                                Val::var(Var::Builtin(Builtin::BoolType)),
                            )
                        } else {
                            return Err(TypeError::Other(format!("invalid operator: {}", tok)));
                        }
                    }
                    ast::Expr::If(_) => todo!(),
                    ast::Expr::Box(_) => todo!(),
                    ast::Expr::Type(_) => todo!(),
                    ast::Expr::GroupedExpr(e) => match e.expr() {
                        Some(e) => e.infer(cxt),
                        // Assume () is the unit value by default, it's only the unit type if it's checked against Type
                        None => (
                            Expr::var(Var::Builtin(Builtin::Unit)),
                            Val::var(Var::Builtin(Builtin::UnitType)),
                        ),
                    },
                    ast::Expr::Tuple(_) => todo!(),
                    ast::Expr::EffPat(_) => todo!(),
                    ast::Expr::Binder(_) => todo!(),
                    ast::Expr::StructInit(_) => todo!(),
                }
            })
        };
        // TODO auto-applying implicits (probably? only allowing them on function calls is also an option to consider)
        match result() {
            Ok(x) => x,
            Err(e) => {
                cxt.error(self.span(), e);
                (Expr::Error, Val::Error)
            }
        }
    }
}
