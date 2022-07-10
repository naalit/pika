use crate::{common::*, intern_key};

mod cxt;
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
use var::*;

use self::unify::CheckReason;

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

    fn all_errors(&self, file: File) -> Vec<(Error, SplitId)>;
}

fn all_errors(db: &dyn Elaborator, file: File) -> Vec<(Error, SplitId)> {
    let splits = db.all_split_ids(file);
    let mut errors = Vec::new();
    for split in splits {
        if let Some(res) = db.parse(file, split) {
            errors.extend(res.errors.into_iter().map(|x| (x, split)));
        }
        let def = db.def(DefLoc::Root(file, split));
        if let Some(res) = db.def_type(def) {
            errors.extend(res.errors.into_iter().map(|x| (x, split)));
        }
        if let Some(res) = db.def_elab(def) {
            errors.extend(res.errors.into_iter().map(|x| (x, split)));
        }
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
            match adef {
                ast::Def::LetDef(x) => x
                    .pat()?
                    .expr()?
                    .as_let_def_pat(&mut Cxt::new(db, DefCxt::global(def_file(db, def))))
                    .0
                    .map(|x| x.0),
                ast::Def::FunDef(x) => Some(x.name()?.name(db).0),
                ast::Def::TypeDef(x) => Some(x.name()?.name(db).0),
                ast::Def::TypeDefShort(x) => Some(x.name()?.name(db).0),
                ast::Def::TypeDefStruct(x) => Some(x.name()?.name(db).0),
            }
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
    let mut cxt = Cxt::new(db, cxt);
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
    let mut cxt = Cxt::new(db, cxt);
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefElabResult {
    pub result: Option<Definition>,
    pub errors: Vec<Error>,
    pub children: Vec<(Def, DefNode)>,
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

impl ast::Expr {
    fn as_let_def_pat(&self, cxt: &mut Cxt) -> (Option<SName>, Option<ast::Ty>) {
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
                        "Binder (_:_) is not allowed to be nested in another binder",
                    );
                }
                (name, x.ty())
            }
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
                        .check(Val::Type, cxt, &CheckReason::UsedAsType)
                        .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                        .eval(&mut cxt.env()),
                ),
                _ => {
                    // Infer the type from the value if possible
                    let def = cxt.db.def_elab_n(def_node);
                    match def.result {
                        Some(Definition { ty, .. }) => Some(
                            ty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                                .eval(&mut cxt.env()),
                        ),
                        _ => None,
                    }
                }
            },
            ast::Def::FunDef(x) => {
                // [a, b] [c, d] (e, f) => ...
                // -->
                // [a, b, c, d] => ((e, f) => ...)

                cxt.push();
                let implicit: Vec<_> = x
                    .imp_par()
                    .into_iter()
                    .flat_map(|x| x.pars())
                    .flat_map(|x| {
                        // [] means [_: ()]
                        x.par().map(|x| x.infer(cxt)).unwrap_or_else(|| {
                            vec![Par {
                                name: (cxt.db.name("_".to_string()), x.span()),
                                ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                            }]
                        })
                    })
                    .collect();
                let explicit: Vec<_> = x.exp_par().map(|x| x.infer(cxt)).unwrap_or(Vec::new());
                let bty = x.ret_ty().and_then(|x| x.expr())?;
                let bty = bty.check(Val::Type, cxt, &CheckReason::UsedAsType);
                let bty = bty.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                cxt.pop();

                // We have to evaluate this outside of the scope
                let mut ty = if explicit.is_empty() {
                    bty
                } else {
                    Expr::Fun(EClos {
                        class: Pi(Expl),
                        params: explicit.clone(),
                        body: Box::new(bty),
                    })
                };
                if !implicit.is_empty() {
                    ty = Expr::Fun(EClos {
                        class: Pi(Impl),
                        params: implicit.clone(),
                        body: Box::new(ty),
                    });
                }
                let ty = ty
                    .eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))
                    .eval(&mut cxt.env());

                Some(ty)
            }
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
                        // inline metas in the term
                        let body = body.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                        Some(Definition {
                            name,
                            ty: Box::new(ty.quote(cxt.size(), Some(&cxt.mcxt))),
                            body: Box::new(Expr::Spanned(x.body().unwrap().span(), Box::new(body))),
                        })
                    }
                    (Some(name), Some(pty)) => {
                        // We already elaborated the type, so avoid doing that twice
                        let ty = cxt.db.def_type_n(def_node).result?;
                        let body = x.body()?.expr()?.check(
                            ty.clone(),
                            cxt,
                            &CheckReason::GivenType(pty.span()),
                        );
                        let body = body.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt));
                        Some(Definition {
                            name,
                            ty: Box::new(Expr::Spanned(
                                pty.span(),
                                Box::new(ty.quote(cxt.size(), Some(&cxt.mcxt))),
                            )),
                            body: Box::new(Expr::Spanned(x.body().unwrap().span(), Box::new(body))),
                        })
                    }
                    (None, _) => None,
                }
            }
            ast::Def::FunDef(x) => {
                // [a, b] [c, d] (e, f) => ...
                // -->
                // [a, b, c, d] => ((e, f) => ...)

                cxt.push();
                let implicit: Vec<_> = x
                    .imp_par()
                    .into_iter()
                    .flat_map(|x| x.pars())
                    .flat_map(|x| {
                        // [] means [_: ()]
                        x.par().map(|x| x.infer(cxt)).unwrap_or_else(|| {
                            vec![Par {
                                name: (cxt.db.name("_".to_string()), x.span()),
                                ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                            }]
                        })
                    })
                    .collect();
                let explicit: Vec<_> = x.exp_par().map(|x| x.infer(cxt)).unwrap_or(Vec::new());
                let (body, bty) = match x.ret_ty().and_then(|x| x.expr()) {
                    Some(bty) => {
                        let span = bty.span();
                        let bty = bty.check(Val::Type, cxt, &CheckReason::UsedAsType);
                        let bty = bty.eval(&mut cxt.env());
                        let body = x
                            .body()
                            .and_then(|x| x.expr())
                            .map(|x| x.check(bty.clone(), cxt, &CheckReason::GivenType(span)))
                            .unwrap_or_else(|| {
                                cxt.error(self.span(), "Missing function body");
                                Expr::Error
                            });
                        (body, bty)
                    }
                    None => x
                        .body()
                        .and_then(|x| x.expr())
                        .map(|x| x.infer(cxt))
                        .unwrap_or_else(|| {
                            cxt.error(self.span(), "Missing function body");
                            (Expr::Error, Val::Error)
                        }),
                };
                let bty = bty.quote(cxt.size(), None);
                cxt.pop();

                // We have to evaluate this outside of the scope
                let mut ty = if explicit.is_empty() {
                    bty
                } else {
                    Expr::Fun(EClos {
                        class: Pi(Expl),
                        params: explicit.clone(),
                        body: Box::new(bty),
                    })
                };
                if !implicit.is_empty() {
                    ty = Expr::Fun(EClos {
                        class: Pi(Impl),
                        params: implicit.clone(),
                        body: Box::new(ty),
                    });
                }
                let ty = ty.eval(&mut cxt.env());
                let mut term = if explicit.is_empty() {
                    body
                } else {
                    Expr::Fun(EClos {
                        class: Lam(Expl),
                        params: explicit,
                        body: Box::new(body),
                    })
                };
                if !implicit.is_empty() {
                    term = Expr::Fun(EClos {
                        class: Lam(Impl),
                        params: implicit,
                        body: Box::new(term),
                    });
                }

                Some(Definition {
                    name: x.name()?.name(cxt.db),
                    ty: Box::new(ty.quote(cxt.size(), Some(&cxt.mcxt))),
                    body: Box::new(term.eval_quote(&mut cxt.env(), cxt.size(), Some(&cxt.mcxt))),
                })
            }
            ast::Def::TypeDef(_) => todo!(),
            ast::Def::TypeDefShort(_) => todo!(),
            ast::Def::TypeDefStruct(_) => todo!(),
        }
    }
}

impl ast::Lit {
    pub(self) fn to_literal(&self, cxt: &mut Cxt) -> Result<Literal, String> {
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
            let num = lex_number(l.text()).map_err(|e| format!("Invalid literal: {}", e))?;
            match num {
                NumLiteral::IPositive(i) => {
                    let meta = cxt
                        .mcxt
                        .unscoped_meta(MetaBounds::int_type(false, i), self.span());
                    Ok(Literal::Int(i, Err((false, meta))))
                }
                NumLiteral::INegative(i) => {
                    let meta = cxt
                        .mcxt
                        .unscoped_meta(MetaBounds::int_type(true, i as u64), self.span());
                    Ok(Literal::Int(i as u64, Err((true, meta))))
                }
                NumLiteral::Float(_) => todo!(),
            }
        } else {
            todo!("invalid literal: {:?}", self.syntax());
        }
    }
}

impl ast::TermPar {
    fn elab(&self, cxt: &mut Cxt) -> Vec<Par> {
        self
            .expr()
            .map(|x| x.as_args())
            .into_iter()
            .flatten()
            .map(|x| {
                let par = match x {
                    Ok(ast::Expr::Binder(x)) => {
                        let (name, ty) = x
                            .pat()
                            .and_then(|x| x.expr())
                            .map(|x| {
                                x.as_simple_pat(cxt.db).unwrap_or_else(|| {
                                    todo!("move non-trivial pats to rhs")
                                })
                            })
                            .unwrap_or((None, None));
                        let name = name.unwrap_or_else(|| (cxt.db.name("_".to_string()), x.span()));
                        if ty.is_some() {
                            cxt.error(x.pat().unwrap().span(), "Binder '_: _' not allowed in pattern of another binder");
                        }
                        let ty = x.ty().and_then(|x| x.expr()).map(|x| x.check(Val::Type, cxt, &CheckReason::UsedAsType)).unwrap_or_else(|| {
                            cxt.error(x.span(), "Binder '_: _' missing type on right-hand side; use '_' to infer type");
                            Expr::Error
                        });
                        Par {
                            name,
                            ty,
                        }
                    }
                    Ok(x) => {
                        let ty = x.check(Val::Type, cxt, &CheckReason::UsedAsType);
                        Par {
                            name: (cxt.db.name("_".to_string()), x.span()),
                            ty,
                        }
                    }
                    Err(span) => Par {
                        name: (cxt.db.name("_".to_string()), span),
                        ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                    },
                };
                // Define each parameter so it can be used by the types of the rest
                cxt.define_local(par.name, par.ty.clone().eval(&mut cxt.env()), None);
                par
            })
            .collect()
    }
}

impl ast::PatPar {
    fn infer(&self, cxt: &mut Cxt) -> Vec<Par> {
        self.pat()
            .and_then(|x| x.expr())
            .map(|x| x.as_args())
            .into_iter()
            .flatten()
            .map(|x| {
                let p = x.as_ref().map(|x| {
                    x.as_simple_pat(cxt.db)
                        .unwrap_or_else(|| todo!("move non-trivial pats to rhs"))
                });
                let par = match p {
                    Ok((name, ty)) => {
                        let name = name.unwrap_or_else(|| {
                            (cxt.db.name("_".to_string()), x.as_ref().unwrap().span())
                        });
                        let ty = ty
                            .map(|x| x.check(Val::Type, cxt, &CheckReason::UsedAsType))
                            .unwrap_or_else(|| {
                                cxt.mcxt.new_meta(
                                    cxt.locals(),
                                    MetaBounds::new(Val::Type),
                                    x.unwrap().span(),
                                )
                            });
                        Par { name, ty }
                    }
                    Err(span) => Par {
                        name: (cxt.db.name("_".to_string()), *span),
                        ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                    },
                };
                // Define each parameter so it can be used by the types of the rest
                cxt.define_local(par.name, par.ty.clone().eval(&mut cxt.env()), None);
                par
            })
            .collect()
    }
}

impl ast::Pair {
    fn elab_sigma(&self, cxt: &mut Cxt) -> Result<Expr, TypeError> {
        match self.lhs() {
            Some(ast::Expr::Binder(x)) => {
                let name = x
                    .pat()
                    .and_then(|x| x.expr())
                    .map(|x| match x {
                        ast::Expr::Var(x) => Some(x.name(cxt.db)),
                        _ => None,
                    })
                    // Allow (: I32, I32) as (_: I32, I32)
                    // this is mostly useful to disambiguate between pair and sigma in inferred context
                    .unwrap_or_else(|| Some((cxt.db.name("_".to_string()), x.span())));

                let ty = x
                    .ty()
                    .and_then(|x| x.expr())
                    .ok_or("Expected type after ':' in binder")?
                    .check(Val::Type, cxt, &CheckReason::UsedAsType);
                let vty = ty.clone().eval(&mut cxt.env());

                if let Some(name) = name {
                    cxt.push();
                    cxt.define_local(name, vty, None);
                    let body = self
                        .rhs()
                        .ok_or("Missing right-hand side type in pair type")?
                        .check(Val::Type, cxt, &CheckReason::UsedAsType);
                    cxt.pop();
                    Ok(Expr::Fun(EClos {
                        class: Sigma,
                        params: vec![Par { name, ty }],
                        body: Box::new(body),
                    }))
                } else {
                    // We have a more complicated pattern on the lhs, so move it to a case on the rhs
                    let name = (cxt.db.name("_".to_string()), x.pat().unwrap().span());
                    cxt.push();
                    cxt.define_local(name, vty.clone(), None);
                    let (case, cty) = self::pattern::elab_case(
                        vty,
                        CheckReason::GivenType(x.ty().map(|x| x.span()).unwrap_or(x.span())),
                        std::iter::once((
                            x.pat().and_then(|x| x.expr()),
                            x.pat().map(|x| x.span()).unwrap_or(x.span()),
                            self.rhs(),
                        )),
                        &mut Some((Val::Type, CheckReason::UsedAsType)),
                        cxt,
                    );
                    cxt.pop();
                    Ok(Expr::Fun(EClos {
                        class: Sigma,
                        params: vec![Par { name, ty }],
                        body: Box::new(Expr::Elim(
                            Box::new(Expr::var(Var::Local(name, Idx::zero()))),
                            Box::new(Elim::Case(case, cty)),
                        )),
                    }))
                }
            }
            Some(pa) => {
                let a = pa.check(Val::Type, cxt, &CheckReason::UsedAsType);
                // We need to elaborate b at the proper size so the indices are correct
                let name = (cxt.db.name("_".to_string()), pa.span());
                let va = a.clone().eval(&mut cxt.env());
                cxt.push();
                // TODO can we just use Val::Error or something? it should be impossible to use this...?
                cxt.define_local(name, va, None);
                let b = self
                    .rhs()
                    .ok_or("Missing right-hand side type in pair type")?
                    .check(Val::Type, cxt, &CheckReason::UsedAsType);
                cxt.pop();
                Ok(Expr::Fun(EClos {
                    class: Sigma,
                    params: vec![Par { name, ty: a }],
                    body: Box::new(b),
                }))
            }
            None => Err(TypeError::Other(Doc::start(
                "Missing left-hand side type in pair type",
            ))),
        }
    }
}

enum ParamTys<'a, 'b> {
    Impl(&'a mut VecDeque<&'b Par>),
    Expl(Expr),
}
impl<'b> ParamTys<'_, 'b> {
    fn zip_with<T>(self, it: impl ExactSizeIterator<Item = T>) -> Vec<(Option<Expr>, Vec<T>)> {
        match self {
            ParamTys::Impl(v) => it
                .map(|x| (v.pop_front().map(|par| par.ty.clone()), vec![x]))
                .collect(),
            ParamTys::Expl(t) => {
                let len = it.len();
                let (t, vec) =
                    it.enumerate()
                        .fold((Some(t), Vec::new()), |(t, mut vec), (i, x)| match t {
                            Some(Expr::Fun(EClos {
                                class: Sigma,
                                mut params,
                                body,
                            })) if i + 1 != len => {
                                assert_eq!(params.len(), 1);
                                let ty = params.pop().unwrap().ty;
                                vec.push((Some(ty), vec![x]));
                                (Some(*body), vec)
                            }
                            Some(t) => {
                                vec.push((Some(t), vec![x]));
                                (None, vec)
                            }
                            None => {
                                vec.last_mut().unwrap().1.push(x);
                                (None, vec)
                            }
                        });
                if t.is_some() {
                    todo!("this should mean there were no parameters")
                }
                vec
            }
        }
    }
}

fn check_params(
    pars: impl Iterator<Item = (Option<ast::PatPar>, RelSpan)>,
    tys: ParamTys,
    cxt: &mut Cxt,
    reason: &CheckReason,
) -> Vec<Par> {
    tys.zip_with(
        pars.flat_map(|(x, span)| {
            x.and_then(|x| x.pat())
                .and_then(|x| x.expr())
                .map(|x| x.as_args())
                .unwrap_or_else(|| vec![Err(span)])
        })
        .collect::<Vec<_>>()
        .into_iter(),
    )
    .into_iter()
    .map(|(ty, mut xs)| {
        // [] means [_: ()]
        let x = match xs.len() {
            1 => xs.pop().unwrap(),
            _ => todo!("probably should do pattern elaboration"),
        };
        let xspan = x.as_ref().map_or_else(|x| *x, |x| x.span());
        let par = match ty {
            Some(ety) => {
                let vety = ety.clone().eval(&mut cxt.env());
                match x.map(|x| x.as_simple_pat(cxt.db)) {
                    Ok(Some((name, ty))) => {
                        let ty = if let Some(ty) = ty {
                            let ty = ty.check(Val::Type, cxt, &CheckReason::UsedAsType);
                            cxt.mcxt
                                .unify(ty.clone().eval(&mut cxt.env()), vety, cxt.size(), reason)
                                .unwrap_or_else(|e| cxt.error(xspan, e));
                            ty
                        } else {
                            // This is fine since we keep cxt.size() at the level that the parameters expect
                            ety
                        };
                        let name = name.unwrap_or_else(|| (cxt.db.name("_".to_string()), xspan));
                        Par { name, ty }
                    }
                    Ok(None) => todo!("move non-trivial patterns to rhs"),
                    Err(span) => {
                        cxt.mcxt
                            .unify(
                                Val::var(Var::Builtin(Builtin::UnitType)),
                                vety,
                                cxt.size(),
                                reason,
                            )
                            .unwrap_or_else(|e| cxt.error(span, e));
                        let name = (cxt.db.name("_".to_string()), span);
                        Par {
                            name,
                            ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                        }
                    }
                }
            }
            // TODO better error here (include type)
            None => {
                let name = x
                    .ok()
                    .and_then(|x| x.as_simple_pat(cxt.db))
                    .and_then(|x| x.0)
                    .unwrap_or_else(|| (cxt.db.name("_".to_string()), xspan));
                cxt.error(
                    xspan,
                    Doc::start("Lambda contains extra parameter ")
                        .add(cxt.db.lookup_name(name.0), Doc::COLOR1)
                        .add(" which is not present in expected type", ()),
                );
                Par {
                    name,
                    ty: Expr::Error,
                }
            }
        };
        cxt.define_local(par.name, par.ty.clone().eval(&mut cxt.env()), None);
        par
    })
    .collect()
}

impl Expr {
    /// If `term` of type `ty` takes implicit parameters, insert metas to apply them.
    fn insert_metas(
        self,
        ty: Val,
        imp_args: Option<ast::ImpArgs>,
        span: RelSpan,
        cxt: &mut Cxt,
    ) -> (Expr, Val) {
        match ty {
            Val::Fun(clos) if clos.class == Pi(Impl) => {
                let mut args: VecDeque<_> = imp_args
                    .into_iter()
                    .flat_map(|x| x.args())
                    .flat_map(|x| x.expr().map(|x| x.as_args()).unwrap_or(vec![Err(x.span())]))
                    .collect();
                let mut targs: Vec<Expr> = Vec::new();
                let par_ty = clos.par_ty();
                let rty = clos.elab_with(|aty| match args.pop_front() {
                    Some(arg) => match arg {
                        Ok(arg) => {
                            let arg = arg.check(aty, cxt, &CheckReason::ArgOf(span));
                            targs.push(arg.clone());
                            arg.eval(&mut cxt.env())
                        }
                        Err(span) => {
                            if let Err(e) = cxt.mcxt.unify(
                                Val::var(Var::Builtin(Builtin::UnitType)),
                                aty,
                                cxt.size(),
                                &CheckReason::ArgOf(span),
                            ) {
                                cxt.error(span, e);
                                Val::Error
                            } else {
                                targs.push(Expr::var(Var::Builtin(Builtin::Unit)));
                                Val::var(Var::Builtin(Builtin::Unit))
                            }
                        }
                    },
                    None => {
                        // Apply a new metavariable
                        let e = cxt.mcxt.new_meta(cxt.locals(), MetaBounds::new(aty), span);
                        targs.push(e.clone());
                        e.eval(&mut cxt.env())
                    }
                });
                let ty = par_ty.quote(cxt.size(), None);

                fn make_arg(
                    mut v: impl Iterator<Item = Expr>,
                    ty: Expr,
                    cxt: &Cxt,
                ) -> Option<Expr> {
                    let a = v.next()?;
                    let ty2 = match ty.clone() {
                        Expr::Fun(EClos {
                            class: Sigma, body, ..
                        }) => {
                            let mut env = cxt.env();
                            env.push(Some(a.clone().eval(&mut cxt.env())));
                            body.eval_quote(&mut env, cxt.size(), None)
                        }
                        _ => Expr::Error,
                    };
                    match make_arg(v, ty2, cxt) {
                        Some(b) => Some(Expr::Pair(Box::new(a), Box::new(b), Box::new(ty))),
                        None => Some(a),
                    }
                }
                let arg = make_arg(targs.into_iter(), ty, cxt).unwrap();

                (
                    Expr::Elim(Box::new(self), Box::new(Elim::App(Impl, arg))),
                    rty,
                )
            }
            _ => (self, ty),
        }
    }
}

impl ast::Expr {
    fn check(&self, mut ty: Val, cxt: &mut Cxt, reason: &CheckReason) -> Expr {
        ty.inline_head(&mut cxt.env(), &cxt.mcxt);
        let result = || {
            match (self, ty) {
                (ast::Expr::GroupedExpr(x), ty) if x.expr().is_some() => {
                    Ok(x.expr().unwrap().check(ty, cxt, reason))
                }

                // Infer assumes (a, b) is a pair, so elaborate as sigma if checking against Type
                (ast::Expr::Pair(x), Val::Type) => x.elab_sigma(cxt),
                // Same for ()
                (ast::Expr::GroupedExpr(x), Val::Type) if x.expr().is_none() => {
                    Ok(Expr::var(Var::Builtin(Builtin::UnitType)))
                }

                // Check pair against sigma and lambda against pi
                (ast::Expr::Pair(x), Val::Fun(clos)) if clos.class == Sigma => {
                    assert_eq!(clos.params.len(), 1);
                    let ety = clos.clone().quote(cxt.size(), None);
                    let a = x.lhs().ok_or("Missing pair left-hand side value")?.check(
                        clos.par_ty(),
                        cxt,
                        reason,
                    );
                    // TODO make this lazy
                    let va = a.clone().eval(&mut cxt.env());
                    let bty = clos.apply(va);
                    let b = x
                        .rhs()
                        .ok_or("Missing pair right-hand side value")?
                        .check(bty, cxt, reason);
                    Ok(Expr::Pair(
                        Box::new(a),
                        Box::new(b),
                        Box::new(Expr::Fun(ety)),
                    ))
                }
                (ast::Expr::Lam(x), Val::Fun(clos)) if matches!(clos.class, Pi(_)) => {
                    // [a, b] [c, d] (e, f) => ...
                    // -->
                    // [a, b, c, d] => ((e, f) => ...)

                    let mut clos = clos.move_env(&mut cxt.env());

                    cxt.push();
                    let mut implicit_tys: VecDeque<_> = match clos.class.icit() {
                        Some(Impl) => clos.params.iter().collect(),
                        _ => VecDeque::new(),
                    };
                    let mut implicit: Vec<_> = check_params(
                        x.imp_par()
                            .into_iter()
                            .flat_map(|x| x.pars())
                            .map(|x| (x.par(), x.span())),
                        ParamTys::Impl(&mut implicit_tys),
                        cxt,
                        reason,
                    );
                    // Add any implicit parameters in the type but not the lambda to the lambda
                    // Make sure, however, that they can't actually be accessed by name by code in the lambda
                    for par in implicit_tys {
                        cxt.define_local(
                            (par.name.0.inaccessible(cxt.db), par.name.1),
                            par.ty.clone().eval(&mut cxt.env()),
                            None,
                        );
                        implicit.push(par.clone());
                    }
                    if !implicit.is_empty() {
                        // This is all fine since we keep cxt.size() at the level that the parameters expect
                        assert_eq!(cxt.size(), clos.env.size + clos.params.len());
                        let mut body = clos.body.eval(&mut cxt.env());
                        body.inline_head(&mut cxt.env(), &cxt.mcxt);
                        match body {
                            Val::Fun(c) if c.class == Pi(Expl) => {
                                clos = *c;
                                if clos.env.size != cxt.size() {
                                    clos = clos.move_env(&mut cxt.env());
                                }
                            }
                            body => {
                                if x.exp_par().is_some() {
                                    // TODO better error here (include type)
                                    return Err("Lambda contains explicit parameters which are not present in expected type".into());
                                } else {
                                    clos = VClos {
                                        class: Pi(Expl),
                                        params: Vec::new(),
                                        env: cxt.env(),
                                        body: body.quote(cxt.size(), None),
                                    }
                                }
                            }
                        }
                    }

                    let explicit = if let Some(e) = x.exp_par() {
                        check_params(
                            std::iter::once((Some(e), x.span())),
                            ParamTys::Expl(clos.par_ty().quote(cxt.size(), None)),
                            cxt,
                            reason,
                        )
                    } else {
                        if !clos.params.is_empty() {
                            return Err(Doc::start("Expected explicit parameters of type '")
                                .chain(
                                    clos.par_ty()
                                        .quote(cxt.size(), Some(&cxt.mcxt))
                                        .pretty(cxt.db),
                                )
                                .add("'", ())
                                .into());
                        }
                        Vec::new()
                    };

                    assert_eq!(cxt.size(), clos.env.size + clos.params.len());
                    let bty = clos.body.eval(&mut cxt.env());
                    let body = x
                        .body()
                        .and_then(|x| x.expr())
                        .ok_or("Missing body for lambda")?
                        .check(bty, cxt, reason);
                    cxt.pop();

                    let mut term = if explicit.is_empty() {
                        body
                    } else {
                        Expr::Fun(EClos {
                            class: Lam(Expl),
                            params: explicit,
                            body: Box::new(body),
                        })
                    };
                    if !implicit.is_empty() {
                        term = Expr::Fun(EClos {
                            class: Lam(Impl),
                            params: implicit,
                            body: Box::new(term),
                        });
                    }
                    Ok(term)
                }

                // Propagate through case/do/etc.
                (ast::Expr::Case(case), ty) => {
                    let mut rty = Some((ty, reason.clone()));
                    let (scrutinee, case, cty) = case.elaborate(&mut rty, cxt);
                    Ok(Expr::Elim(
                        Box::new(scrutinee),
                        Box::new(Elim::Case(case, cty)),
                    ))
                }
                (ast::Expr::Do(d), ty) => {
                    let mut rty = Some((ty, reason.clone()));
                    let expr = d.elaborate(&mut rty, cxt);
                    Ok(expr)
                }

                // Insert implicit lambdas when checking against an implicit function type
                // TODO this should probably be off by default, or at least more restricted
                // But unfortunately it's kind of required for certain fancy dependent type things
                // (like dependent composition)
                (_, Val::Fun(clos)) if clos.class == Pi(Impl) => {
                    let clos = clos.move_env(&mut cxt.env());
                    let mut params = clos.params.clone();
                    let bty = clos.open(cxt.size());

                    cxt.push();
                    for i in &mut params {
                        i.name.0 = i.name.0.inaccessible(cxt.db);
                        cxt.define_local(i.name, i.ty.clone().eval(&mut cxt.env()), None);
                    }

                    let body = self.check(bty, cxt, reason);

                    let clos = EClos {
                        class: Lam(Impl),
                        params,
                        body: Box::new(body),
                    };

                    cxt.pop();
                    Ok(Expr::Fun(clos))
                }

                (_, ty) => {
                    let (a, ity) = self.infer(cxt);
                    let (a, ity) = match &ty {
                        Val::Fun(clos) if clos.class == Pi(Impl) => (a, ity),
                        _ => a.insert_metas(ity, None, self.span(), cxt),
                    };
                    cxt.mcxt.unify(ity, ty, cxt.size(), reason)?;
                    Ok(a)
                }
            }
        };
        // TODO auto-applying implicits (probably? only allowing them on function calls is also an option to consider)
        match result() {
            Ok(x) => Expr::Spanned(self.span(), Box::new(x)),
            Err(e) => {
                cxt.error(self.span(), e);
                Expr::Error
            }
        }
    }

    fn as_args(self) -> Vec<Result<ast::Expr, RelSpan>> {
        match self {
            ast::Expr::GroupedExpr(ref x) => x
                .expr()
                .map(|x| x.as_args())
                .unwrap_or_else(|| vec![Err(x.span())]),
            ast::Expr::Pair(x) => {
                let mut v = x
                    .rhs()
                    .map(|x| x.as_args())
                    .unwrap_or_else(|| vec![Err(x.span())]);
                v.insert(0, x.lhs().ok_or(x.span()));
                v
            }
            _ => vec![Ok(self)],
        }
    }

    fn as_simple_pat(&self, db: &dyn Elaborator) -> Option<(Option<SName>, Option<ast::Expr>)> {
        match self {
            ast::Expr::Var(x) => Some((Some(x.name(db)), None)),
            ast::Expr::Binder(x) => {
                let (name, old_ty) = x.pat()?.expr()?.as_simple_pat(db)?;
                if old_ty.is_some() {
                    // ((x: A): B) is an error, let the actual pattern compilation code handle it
                    None
                } else {
                    Some((name, x.ty().and_then(|x| x.expr())))
                }
            }
            ast::Expr::GroupedExpr(x) => x
                .expr()
                .map(|x| x.as_simple_pat(db))
                // For (), we return this expression as the type, since it's identical syntactically
                .unwrap_or_else(|| {
                    Some((
                        Some((db.name("_".to_string()), self.span())),
                        Some(self.clone()),
                    ))
                }),
            _ => None,
        }
    }

    fn infer(&self, cxt: &mut Cxt) -> (Expr, Val) {
        // TODO hopefully try {} blocks stabilize soon and this won't be necessary
        let mut result = || {
            Ok({
                match self {
                    ast::Expr::Var(name) => {
                        let name = name.name(cxt.db);
                        if name.0 == cxt.db.name("_".to_string()) {
                            let mty = cxt
                                .mcxt
                                .new_meta(cxt.locals(), MetaBounds::new(Val::Type), self.span())
                                .eval(&mut cxt.env());
                            let meta = cxt.mcxt.new_meta(
                                cxt.locals(),
                                MetaBounds::new(mty.clone()),
                                self.span(),
                            );
                            (meta, mty)
                        } else {
                            let (v, t) = cxt.lookup(name).ok_or(TypeError::NotFound(name.0))?;
                            (Expr::var(v.cvt(cxt.size())), t)
                        }
                    }
                    ast::Expr::Lam(x) => {
                        // [a, b] [c, d] (e, f) => ...
                        // -->
                        // [a, b, c, d] => ((e, f) => ...)

                        cxt.push();
                        let implicit: Vec<_> = x
                            .imp_par()
                            .into_iter()
                            .flat_map(|x| x.pars())
                            .flat_map(|x| {
                                // [] means [_: ()]
                                x.par().map(|x| x.infer(cxt)).unwrap_or_else(|| {
                                    vec![Par {
                                        name: (cxt.db.name("_".to_string()), x.span()),
                                        ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                                    }]
                                })
                            })
                            .collect();
                        let explicit: Vec<_> =
                            x.exp_par().map(|x| x.infer(cxt)).unwrap_or(Vec::new());
                        let (body, bty) = x
                            .body()
                            .and_then(|x| x.expr())
                            .ok_or("Missing body for lambda")?
                            .infer(cxt);
                        let bty = bty.quote(cxt.size(), None);
                        cxt.pop();

                        // We have to evaluate this outside of the scope
                        let mut ty = if explicit.is_empty() {
                            bty
                        } else {
                            Expr::Fun(EClos {
                                class: Pi(Expl),
                                params: explicit.clone(),
                                body: Box::new(bty),
                            })
                        };
                        if !implicit.is_empty() {
                            ty = Expr::Fun(EClos {
                                class: Pi(Impl),
                                params: implicit.clone(),
                                body: Box::new(ty),
                            });
                        }
                        let ty = ty.eval(&mut cxt.env());
                        let mut term = if explicit.is_empty() {
                            body
                        } else {
                            Expr::Fun(EClos {
                                class: Lam(Expl),
                                params: explicit,
                                body: Box::new(body),
                            })
                        };
                        if !implicit.is_empty() {
                            term = Expr::Fun(EClos {
                                class: Lam(Impl),
                                params: implicit,
                                body: Box::new(term),
                            });
                        }

                        (term, ty)
                    }
                    ast::Expr::Pi(x) => {
                        // [a, b] [c, d] (e: A, f: B) -> ...
                        // -->
                        // [a, b, c, d] -> ((e: A, f: B) -> ...)

                        cxt.push();
                        let implicit: Vec<_> = x
                            .imp_par()
                            .into_iter()
                            .flat_map(|x| x.pars())
                            .flat_map(|x| {
                                // [] means [_: ()]
                                x.par().map(|x| x.infer(cxt)).unwrap_or_else(|| {
                                    vec![Par {
                                        name: (cxt.db.name("_".to_string()), x.span()),
                                        ty: Expr::var(Var::Builtin(Builtin::UnitType)),
                                    }]
                                })
                            })
                            .collect();
                        let explicit: Vec<_> =
                            x.exp_par().map(|x| x.elab(cxt)).unwrap_or(Vec::new());
                        let body = x
                            .body()
                            .and_then(|x| x.expr())
                            .ok_or("Missing body for function type")?
                            .check(Val::Type, cxt, &CheckReason::UsedAsType);
                        if x.with().is_some() {
                            todo!("implement effects")
                        }
                        cxt.pop();

                        let mut term = if explicit.is_empty() {
                            body
                        } else {
                            Expr::Fun(EClos {
                                class: Pi(Expl),
                                params: explicit.clone(),
                                body: Box::new(body),
                            })
                        };
                        if !implicit.is_empty() {
                            term = Expr::Fun(EClos {
                                class: Pi(Impl),
                                params: implicit.clone(),
                                body: Box::new(term),
                            });
                        }
                        (term, Val::Type)
                    }
                    ast::Expr::App(x) => {
                        let (lhs, mut lhs_ty) = x
                            .lhs()
                            .ok_or("Missing left-hand side of application")?
                            .infer(cxt);
                        lhs_ty.inline_head(&mut cxt.env(), &cxt.mcxt);
                        let mut lhs_span = x.lhs().unwrap().span();
                        if x.member().is_some() {
                            todo!("implement members")
                        }

                        // First handle implicit arguments, then curry and apply explicits
                        let (lhs, lhs_ty) = lhs.insert_metas(lhs_ty, x.imp(), lhs_span, cxt);
                        lhs_span.end = x.imp().map(|x| x.span()).unwrap_or(lhs_span).end;

                        // Apply explicit arguments
                        if let Some(exp) = x.exp() {
                            match lhs_ty {
                                Val::Fun(clos) if matches!(clos.class, Pi(_)) => {
                                    let aty = clos.par_ty();
                                    let exp = exp.check(aty, cxt, &CheckReason::ArgOf(lhs_span));
                                    let vexp = exp.clone().eval(&mut cxt.env());
                                    let rty = clos.apply(vexp);
                                    (
                                        Expr::Elim(Box::new(lhs), Box::new(Elim::App(Expl, exp))),
                                        rty,
                                    )
                                }
                                Val::Error => {
                                    // Still try inferring the argument to catch errors
                                    let (exp, _) = exp.infer(cxt);
                                    (
                                        Expr::Elim(Box::new(lhs), Box::new(Elim::App(Expl, exp))),
                                        Val::Error,
                                    )
                                }
                                lhs_ty => {
                                    return Err(TypeError::NotFunction(
                                        lhs_ty.quote(cxt.size(), Some(&cxt.mcxt)),
                                        lhs_span,
                                    ))
                                }
                            }
                        } else {
                            (lhs, lhs_ty)
                        }
                    }
                    ast::Expr::Do(d) => {
                        let mut rty = None;
                        let expr = d.elaborate(&mut rty, cxt);
                        let rty = rty.map(|(x, _)| x).unwrap_or(Val::Error);
                        (expr, rty)
                    }
                    ast::Expr::Case(case) => {
                        let mut rty = None;
                        let (scrutinee, case, cty) = case.elaborate(&mut rty, cxt);
                        let rty = rty.map(|(x, _)| x).unwrap_or(Val::Error);
                        (
                            Expr::Elim(Box::new(scrutinee), Box::new(Elim::Case(case, cty))),
                            rty,
                        )
                    }
                    ast::Expr::Lit(l) => match l.to_literal(cxt) {
                        Ok(l) => (
                            Expr::Lit(l),
                            match l {
                                Literal::Int(_, ty) => match ty {
                                    Ok(t) => Val::var(Var::Builtin(Builtin::IntType(t))),
                                    Err((_, m)) => Val::var(Var::Meta(m)),
                                },
                                Literal::F64(_) => todo!(),
                                Literal::F32(_) => todo!(),
                                Literal::String(_) => Val::var(Var::Builtin(Builtin::StringType)),
                            },
                        ),
                        Err(e) => {
                            cxt.error(self.span(), e);
                            (Expr::Error, Val::Error)
                        }
                    },
                    ast::Expr::BinOp(x) => {
                        let tok = x.op().ok_or("missing operator")?;
                        let tok = tok
                            .syntax()
                            .unwrap()
                            .children_with_tokens()
                            .find_map(|x| x.as_token().map(|x| x.kind()).filter(|x| x.is_binop()))
                            .unwrap_or(crate::parsing::SyntaxKind::Error);

                        if let Some(op) = ArithOp::from_tok(tok) {
                            let (a, ty) = x
                                .a()
                                .ok_or_else(|| {
                                    TypeError::Other(
                                        Doc::start("missing left operand for operator ")
                                            .add(tok, Doc::COLOR1),
                                    )
                                })?
                                .infer(cxt);
                            let b = x
                                .b()
                                .ok_or_else(|| {
                                    TypeError::Other(
                                        Doc::start("missing right operand for operator ")
                                            .add(tok, Doc::COLOR1),
                                    )
                                })?
                                .check(
                                    ty.clone(),
                                    cxt,
                                    &CheckReason::MustMatch(x.a().unwrap().span()),
                                );
                            (
                                Expr::Elim(
                                    Box::new(Expr::var(Var::Builtin(Builtin::ArithOp(op)))),
                                    Box::new(Elim::App(
                                        Expl,
                                        Expr::Pair(
                                            Box::new(a),
                                            Box::new(b),
                                            Box::new(Expr::Fun(EClos {
                                                class: Sigma,
                                                params: vec![Par {
                                                    name: (
                                                        cxt.db.name("_".into()),
                                                        x.a().unwrap().span(),
                                                    ),
                                                    ty: ty.clone().quote(cxt.size(), None),
                                                }],
                                                body: Box::new(
                                                    ty.clone().quote(cxt.size().inc(), None),
                                                ),
                                            })),
                                        ),
                                    )),
                                ),
                                ty,
                            )
                        } else if let Some(op) = CompOp::from_tok(tok) {
                            let (a, ty) = x
                                .a()
                                .ok_or_else(|| {
                                    TypeError::Other(
                                        Doc::start("missing left operand for operator ")
                                            .add(tok, Doc::COLOR1),
                                    )
                                })?
                                .infer(cxt);
                            let b = x
                                .b()
                                .ok_or_else(|| {
                                    TypeError::Other(
                                        Doc::start("missing right operand for operator ")
                                            .add(tok, Doc::COLOR1),
                                    )
                                })?
                                .check(
                                    ty.clone(),
                                    cxt,
                                    &CheckReason::MustMatch(x.a().unwrap().span()),
                                );
                            (
                                Expr::Elim(
                                    Box::new(Expr::var(Var::Builtin(Builtin::CompOp(op)))),
                                    Box::new(Elim::App(
                                        Expl,
                                        Expr::Pair(
                                            Box::new(a),
                                            Box::new(b),
                                            Box::new(Expr::Fun(EClos {
                                                class: Sigma,
                                                params: vec![Par {
                                                    name: (
                                                        cxt.db.name("_".into()),
                                                        x.a().unwrap().span(),
                                                    ),
                                                    ty: ty.clone().quote(cxt.size(), None),
                                                }],
                                                body: Box::new(ty.quote(cxt.size().inc(), None)),
                                            })),
                                        ),
                                    )),
                                ),
                                Val::var(Var::Builtin(Builtin::BoolType)),
                            )
                        } else {
                            return Err(TypeError::Other(
                                Doc::start("Invalid operator ").add(tok, Doc::COLOR1),
                            ));
                        }
                    }
                    ast::Expr::If(_) => todo!(),
                    ast::Expr::Box(_) => todo!(),
                    ast::Expr::Type(_) => (Expr::Type, Val::Type),
                    ast::Expr::GroupedExpr(e) => match e.expr() {
                        Some(e) => e.infer(cxt),
                        // Assume () is the unit value by default, it's only the unit type if it's checked against Type
                        None => (
                            Expr::var(Var::Builtin(Builtin::Unit)),
                            Val::var(Var::Builtin(Builtin::UnitType)),
                        ),
                    },
                    ast::Expr::Pair(x) => {
                        if let Some(ast::Expr::Binder(_)) = x.lhs() {
                            let term = x.elab_sigma(cxt)?;
                            return Ok((term, Val::Type));
                        }
                        // Infer a simple non-dependent pair type by default; inference is undecidable with sigma types
                        let (a, aty) = x.lhs().ok_or("missing left value in pair")?.infer(cxt);
                        let (b, bty) = x.rhs().ok_or("missing right value in pair")?.infer(cxt);
                        let aty = aty.quote(cxt.size(), None);
                        // bty is quoted inside of the sigma scope
                        let bty = bty.quote(cxt.size().inc(), None);
                        let ty = Expr::Fun(EClos {
                            class: Sigma,
                            params: vec![Par {
                                name: (cxt.db.name("_".to_string()), x.lhs().unwrap().span()),
                                ty: aty,
                            }],
                            body: Box::new(bty),
                        });
                        let vty = ty.clone().eval(&mut cxt.env());
                        (Expr::Pair(Box::new(a), Box::new(b), Box::new(ty)), vty)
                    }
                    ast::Expr::EffPat(_) => todo!(),
                    ast::Expr::Binder(_) => {
                        return Err(TypeError::Other(Doc::start(
                            "Binder '_: _' not allowed in this context",
                        )))
                    }
                    ast::Expr::StructInit(_) => todo!(),
                }
            })
        };
        // TODO auto-applying implicits (probably? only allowing them on function calls is also an option to consider)
        match result() {
            Ok((x, t)) => (Expr::Spanned(self.span(), Box::new(x)), t),
            Err(e) => {
                cxt.error(self.span(), e);
                (Expr::Error, Val::Error)
            }
        }
    }
}
