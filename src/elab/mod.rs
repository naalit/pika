use crate::common::*;

mod term;
mod val;
mod var;

pub use term::*;
use val::*;
use var::*;

enum TypeError {
    NotFound(Name),
    Unify(Expr, Expr),
    Other(String),
}

struct Scope {
    global: bool,
    names: HashMap<Name, (Var<Idx>, Val)>,
}
impl Scope {
    fn global() -> Self {
        Scope {
            global: false,
            names: HashMap::new(),
        }
    }

    fn new() -> Self {
        Scope {
            global: false,
            names: HashMap::new(),
        }
    }
}

struct Cxt<'a> {
    db: &'a dyn crate::parsing::Parser,
    scopes: Vec<Scope>,
    errors: Vec<Spanned<TypeError>>,
}
impl Cxt<'_> {
    fn scope(&self) -> &Scope {
        self.scopes.last().unwrap()
    }

    fn push(&mut self) {
        self.scopes.push(Scope::new());
    }

    fn pop(&mut self) {
        self.scopes.pop();
    }

    fn lookup(&self, name: Name) -> Option<(Var<Idx>, Val)> {
        self.scopes
            .iter()
            .rev()
            .find_map(|x| x.names.get(&name).cloned())
    }

    fn error(&mut self, span: RelSpan, error: TypeError) {
        self.errors.push((error, span));
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
                        (Expr::var(v), t)
                    }
                    ast::Expr::Lam(_) => todo!(),
                    ast::Expr::Pi(_) => todo!(),
                    ast::Expr::App(_) => todo!(),
                    ast::Expr::Do(_) => todo!(),
                    ast::Expr::Hole(_) => todo!(),
                    ast::Expr::Case(_) => todo!(),
                    ast::Expr::Lit(l) => {
                        if let Some(l) = l.string() {
                            // Process escape sequences to get the string's actual contents
                            // This work is also done by the lexer, which then throws it away;
                            // TODO move all error checking here and simplify the lexer code
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
                            (
                                Expr::Lit(Literal::String(cxt.db.name(buf))),
                                Val::var(Var::Builtin(Builtin::StringType)),
                            )
                        } else {
                            todo!("invalid literal: {:?}", l.syntax());
                        }
                    }
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
                                        implicit: Vec::new(),
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
                                        implicit: Vec::new(),
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
                    ast::Expr::GroupedExpr(_) => todo!(),
                    ast::Expr::Tuple(_) => todo!(),
                    ast::Expr::OrPat(_) => todo!(),
                    ast::Expr::EffPat(_) => todo!(),
                    ast::Expr::Binder(_) => todo!(),
                    ast::Expr::StructInit(_) => todo!(),
                }
            })
        };
        match result() {
            Ok(x) => x,
            Err(e) => {
                cxt.error(self.span(), e);
                (Expr::Error, Val::Error)
            }
        }
    }
}
