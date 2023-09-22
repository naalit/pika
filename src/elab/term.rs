use crate::pretty::Prec;

use super::*;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FunClass {
    /// Sigma types are treated identically to pi types in most cases:
    /// (P: T1, T2(P)) is equivalent for many purposes to (P: T1) -> T2(P).
    /// In a `Clos`, a sigma type may only have one, explicit, parameter.
    /// So their representation is the same (as is that for lambdas), and they're evaluated the same etc.
    /// TODO: we'll eventually annotate pis and probably lambdas with effects, but this will not happen for sigmas.
    Sigma,
    Lam(Icit, CopyClass),
    Pi(Icit, CopyClass),
}
impl FunClass {
    pub fn icit(self) -> Option<Icit> {
        match self {
            Sigma => None,
            Lam(i, _) => Some(i),
            Pi(i, _) => Some(i),
        }
    }
    pub fn copy_class(self) -> CopyClass {
        match self {
            Sigma => CopyClass::Move,
            Lam(_, c) | Pi(_, c) => c,
        }
    }
}
pub use FunClass::{Lam, Pi, Sigma};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // Bitwise are included here since the types match
    Ior,
    Xor,
    And,
    Shl,
    Shr,
}
impl ArithOp {
    pub fn from_tok(tok: crate::parsing::SyntaxKind) -> Option<ArithOp> {
        use crate::parsing::SyntaxKind as Tok;
        Some(match tok {
            Tok::Plus => ArithOp::Add,
            Tok::Minus => ArithOp::Sub,
            Tok::Times => ArithOp::Mul,
            Tok::Div => ArithOp::Div,
            Tok::Mod => ArithOp::Mod,
            Tok::Bar => ArithOp::Ior,
            Tok::Xor => ArithOp::Xor,
            Tok::LShift => ArithOp::Shl,
            Tok::RShift => ArithOp::Shr,
            Tok::BitAnd => ArithOp::And,
            _ => return None,
        })
    }
}
impl std::fmt::Display for ArithOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            ArithOp::Add => "+",
            ArithOp::Sub => "-",
            ArithOp::Mul => "*",
            ArithOp::Div => "/",
            ArithOp::Mod => "%",
            ArithOp::Ior => "|",
            ArithOp::Xor => "^^",
            ArithOp::And => "&",
            ArithOp::Shl => "<<",
            ArithOp::Shr => ">>",
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum CompOp {
    Eq,
    Ne,
    Gt,
    Lt,
    Ge,
    Le,
}
impl CompOp {
    pub fn from_tok(tok: crate::parsing::SyntaxKind) -> Option<CompOp> {
        use crate::parsing::SyntaxKind as Tok;
        Some(match tok {
            Tok::Gt => CompOp::Gt,
            Tok::GtE => CompOp::Ge,
            Tok::Lt => CompOp::Lt,
            Tok::LtE => CompOp::Le,
            Tok::Eq => CompOp::Eq,
            Tok::NEq => CompOp::Ne,
            _ => return None,
        })
    }
}
impl std::fmt::Display for CompOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            CompOp::Eq => "==",
            CompOp::Ne => "!=",
            CompOp::Gt => ">",
            CompOp::Lt => "<",
            CompOp::Ge => ">=",
            CompOp::Le => "<=",
        })
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Builtin {
    IntType(IntType),
    Unit,
    UnitType,
    StringType,
    BoolType,
    ArithOp(ArithOp),
    CompOp(CompOp),
}
impl std::fmt::Display for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Builtin::IntType(i) => write!(f, "{:?}", i),
            Builtin::Unit => write!(f, "()"),
            Builtin::UnitType => write!(f, "()"),
            Builtin::StringType => write!(f, "Str"),
            Builtin::BoolType => write!(f, "Bool"),
            Builtin::ArithOp(op) => write!(f, "{}", op),
            Builtin::CompOp(op) => write!(f, "{}", op),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum IntType {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}
impl IntType {
    pub fn max(self) -> i128 {
        match self {
            IntType::U8 => u8::MAX as _,
            IntType::U16 => u16::MAX as _,
            IntType::U32 => u32::MAX as _,
            IntType::U64 => u64::MAX as _,
            IntType::I8 => i8::MAX as _,
            IntType::I16 => i16::MAX as _,
            IntType::I32 => i32::MAX as _,
            IntType::I64 => i64::MAX as _,
        }
    }

    pub fn min(self) -> i128 {
        match self {
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 => 0,
            IntType::I8 => i8::MIN as _,
            IntType::I16 => i16::MIN as _,
            IntType::I32 => i32::MIN as _,
            IntType::I64 => i64::MIN as _,
        }
    }

    pub fn signed(self) -> bool {
        match self {
            IntType::U8 | IntType::U16 | IntType::U32 | IntType::U64 => false,
            IntType::I8 | IntType::I16 | IntType::I32 | IntType::I64 => true,
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Literal {
    /// Stores the u64 representation of the int and its type
    /// If the type is signed, then the actual value is obtained by a cast to i64
    /// If the type isn't known, we store the meta and a bool for whether it's signed
    Int(u64, Result<IntType, (bool, Meta)>),
    /// Stores a u64 representation of the bits of the f64
    F64(u64),
    /// Stores a u32 representation of the bits of the f32
    F32(u32),
    String(Name),
}
impl Literal {
    pub fn pretty<T: crate::parsing::Parser + ?Sized>(&self, db: &T) -> Doc {
        match self {
            Literal::Int(i, Ok(t)) if t.signed() => Doc::start(*i as i64),
            Literal::Int(i, Err((true, _))) => Doc::start(*i as i64),
            Literal::Int(i, _) => Doc::start(i),
            Literal::F64(i) => Doc::start(f64::from_bits(*i)),
            Literal::F32(i) => Doc::start(f32::from_bits(*i)),
            Literal::String(s) => Doc::start(db.lookup_name(*s)),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Icit {
    Impl,
    Expl,
}
pub use self::Icit::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Par {
    pub name: SName,
    pub ty: Expr,
    pub mutable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConsDef {
    name: SName,
    // TODO ConsId or something
    implicit: Vec<Par>,
    explicit: Vec<Par>,
    ret_ty: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// A let definition is different from a local let statement.
/// Let definitions are unordered, and can't contain patterns other than 'name' or 'name: ty'.
/// Local let statements are ordered, can contain arbitrary patterns, and create local variables rather than definitions.
pub struct Definition {
    pub name: SName,
    pub ty: Box<Expr>,
    pub body: DefBody,
    pub children: Vec<(SplitId, DefNode)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefBody {
    Let(Box<Expr>),
    Type(Vec<(SplitId, RelSpan, Val)>),
    Struct(Vec<(SName, Expr)>),
}

pub trait IsTerm {
    type Clos: std::fmt::Debug + Clone + PartialEq + Eq + std::hash::Hash;
    type Loc: std::fmt::Debug + Clone + Copy + PartialEq + Eq + std::hash::Hash;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Head<L> {
    Var(Var<L>),
}

/* AST -> Term mapping:
    Var,
    Lam, }
    Pi,  }-> one Fun term
    App, -> desugared and split into Member + App
    Do, -> maybe (partially) turned into recursive LetIn and Seq if that helps?
    Hole, -> turned into metavariable
    Case,
    Lit,
    Unit,  }
    BinOp, } -> builtins; and/or are desugared into if then case
    If, -> desugared into case
    Box, -> ? will be handled later
    Type,
    GroupedExpr, -> removed, if empty replaced by Unit
    Tuple, -> Sigma type as Fun or Pair term
    Binder, -> type, usually in Sigma
    StructInit, -> ? will be handled later
*/
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Elim<T: IsTerm> {
    App(Icit, T),
    Member(Def, u64, SName),
    Deref,
    Case(super::pattern::CaseOf<T>, T),
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EClos {
    pub class: FunClass,
    pub params: Vec<Par>,
    pub body: Box<Expr>,
}
#[derive(Debug, Clone, Eq, Hash)]
pub enum Expr {
    Type,
    Head(Head<Idx>),
    Elim(Box<Expr>, Box<Elim<Expr>>),
    Fun(EClos),
    // Do(Vec<Stmt>),
    Lit(Literal),
    /// The last Expr is the type, which can't be inferred from the values
    /// (consider `(I32, 3)`, which may be `(Type, I32)` or `(a: Type, a)`)
    Pair(Box<Expr>, Box<Expr>, Box<Expr>),
    /// (mutable, referent type)
    RefType(bool, Box<Expr>),
    Assign(Box<Expr>, Box<Expr>),
    Ref(bool, Box<Expr>),
    Spanned(RelSpan, Box<Expr>),
    /// (def, fields, type)
    Struct(Def, Vec<Expr>, Box<Expr>),
    Error,
}
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Head(l0), Self::Head(r0)) => l0 == r0,
            (Self::Elim(l0, l1), Self::Elim(r0, r1)) => l0 == r0 && l1 == r1,
            (Self::Fun(l0), Self::Fun(r0)) => l0 == r0,
            (Self::Lit(l0), Self::Lit(r0)) => l0 == r0,
            (Self::Pair(l0, l1, l2), Self::Pair(r0, r1, r2)) => l0 == r0 && l1 == r1 && l2 == r2,
            (Self::RefType(a, x), Self::RefType(b, y)) => a == b && x == y,
            // Ignore spans
            (Self::Spanned(_, l1), Self::Spanned(_, r1)) => l1 == r1,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}
impl IsTerm for Expr {
    type Clos = EClos;
    type Loc = Idx;
}
fn pretty_bind<T: Elaborator + ?Sized>(n: SName, ty: Doc, db: &T, parens: bool) -> Doc {
    if db.name("_".to_string()) == n.0 {
        ty
    } else {
        let doc = n.pretty(db).add(':', ()).space().chain(ty);
        if parens {
            Doc::start('(').chain(doc).add(')', ())
        } else {
            doc
        }
    }
}
impl Builtin {
    pub fn ty(self) -> Val {
        match self {
            Builtin::IntType(_) => Val::Type,
            Builtin::Unit => Val::var(Var::Builtin(Builtin::UnitType)),
            Builtin::UnitType => Val::Type,
            Builtin::StringType => Val::Type,
            Builtin::BoolType => Val::Type,
            // TODO types for operators
            Builtin::ArithOp(_) => Val::Error,
            Builtin::CompOp(_) => Val::Error,
        }
    }

    pub fn name(self, db: &(impl crate::parsing::Parser + ?Sized)) -> Name {
        db.name(format!("{}", self))
    }
}
impl Expr {
    pub fn var(var: Var<Idx>) -> Self {
        Self::Head(Head::Var(var))
    }

    pub fn ty(&self, cxt: &mut Cxt) -> Val {
        match self {
            Expr::Type | Expr::RefType(_, _) => Val::Type,
            Expr::Assign(_, _) => Val::var(Var::Builtin(Builtin::UnitType)),
            Expr::Ref(m, x) => Val::RefType(*m, Box::new(x.ty(cxt))),
            Expr::Head(h) => match h {
                Head::Var(v) => match v {
                    Var::Local(_, i) => cxt.local_ty(i.lvl(cxt.size())),
                    Var::Meta(m) => match cxt.mcxt.meta_ty(*m) {
                        Some(t) => t,
                        None => match cxt.mcxt.lookup(*m) {
                            Some(e) => e.ty(cxt),
                            None => {
                                eprintln!("WARNING: could not get meta type!");
                                Val::Error
                            }
                        },
                    },
                    Var::Builtin(b) => b.ty(),
                    Var::Def(_, d) => cxt
                        .db
                        .def_type(*d)
                        .and_then(|x| x.result)
                        .unwrap_or(Val::Error),
                    Var::Cons(_, c) => {
                        let (d, split) = cxt.db.lookup_cons_id(*c);
                        cxt.db
                            .def_elab(d)
                            .and_then(|x| x.result)
                            .and_then(|x| match x.body {
                                DefBody::Type(v) => v
                                    .into_iter()
                                    .find(|(s, _, _)| *s == split)
                                    .map(|(_, _, ty)| ty),
                                _ => None,
                            })
                            .unwrap_or(Val::Error)
                    }
                },
            },
            Expr::Elim(head, elim) => match &**elim {
                Elim::App(_, x) => match head.ty(cxt) {
                    Val::Fun(clos) if matches!(clos.class, Pi(_, _)) => {
                        clos.apply(x.clone().eval(&mut cxt.env()))
                    }
                    _ => Val::Error,
                },
                Elim::Member(def, idx, _) => {
                    let lhs = (**head).clone().eval(&mut cxt.env());
                    super::elaborate::member_type(&lhs, *def, *idx, cxt)
                }
                Elim::Deref => match head.ty(cxt) {
                    Val::RefType(_, t) => *t,
                    _ => unreachable!(),
                },
                Elim::Case(_, ty) => ty.clone().eval(&mut cxt.env()),
            },
            Expr::Fun(EClos {
                class,
                params,
                body,
            }) => match class {
                Sigma | Pi(_, _) => Val::Type,
                // I don't *think* we need a return type annotation, but there might be edge cases where we do
                Lam(icit, c) => {
                    cxt.push();
                    for Par { name, ty, mutable } in params {
                        cxt.define_local(
                            *name,
                            ty.clone().eval(&mut cxt.env()),
                            None,
                            None,
                            *mutable,
                        );
                    }
                    let ty = Expr::Fun(EClos {
                        class: Pi(*icit, *c),
                        params: params.clone(),
                        body: Box::new(body.ty(cxt).quote(cxt.size(), None)),
                    });
                    cxt.pop();
                    ty.eval(&mut cxt.env())
                }
            },
            Expr::Lit(l) => match l {
                Literal::Int(_, t) => match t {
                    Ok(t) => Val::var(Var::Builtin(Builtin::IntType(*t))),
                    Err((_, m)) => Val::var(Var::Meta(*m)),
                },
                Literal::F64(_) => todo!(),
                Literal::F32(_) => todo!(),
                Literal::String(_) => Val::var(Var::Builtin(Builtin::StringType)),
            },
            Expr::Pair(_, _, ty) | Expr::Struct(_, _, ty) => ty.clone().eval(&mut cxt.env()),
            Expr::Spanned(_, x) => x.ty(cxt),
            Expr::Error => Val::Error,
        }
    }
}
impl Pretty for Expr {
    fn pretty(&self, db: &(impl Elaborator + ?Sized)) -> Doc {
        match self {
            Expr::Spanned(_, x) => x.pretty(db),
            Expr::Type => Doc::none().add("Type", Doc::style_keyword()),
            Expr::Head(h) => match h {
                Head::Var(v) => match v {
                    Var::Local(name, _i) => Doc::start(db.lookup_name(name.0)), //.add('.', ()).add(_i.as_u32(), ()),
                    Var::Meta(m) => Doc::start(m).style(Doc::style_literal()),
                    Var::Builtin(b) => Doc::start(b),
                    // TODO take into account module paths etc.
                    Var::Def(n, _) => n.pretty(db),
                    Var::Cons(n, _) => n.pretty(db),
                },
            },
            Expr::RefType(false, x) => Doc::start('&')
                .chain(x.pretty(db).nest(Prec::App))
                .prec(Prec::App),
            Expr::RefType(true, x) => Doc::start('&')
                .add("mut", Doc::style_keyword())
                .space()
                .chain(x.pretty(db).nest(Prec::App))
                .prec(Prec::App),
            Expr::Assign(place, expr) => place
                .pretty(db)
                .add(" = ", ())
                .chain(expr.pretty(db))
                .prec(Prec::Term),
            Expr::Ref(m, x) => Doc::start("<ref ")
                .add(m, ())
                .add('>', ())
                .space()
                .chain(x.pretty(db).nest(Prec::App))
                .prec(Prec::App),
            Expr::Elim(a, b) => match &**b {
                Elim::App(icit, b) => a
                    .pretty(db)
                    .nest(Prec::App)
                    .chain(match icit {
                        Impl => Doc::none()
                            .space()
                            .add('[', ())
                            .chain(b.pretty(db))
                            .add(']', ()),
                        Expl => Doc::none().space().chain(b.pretty(db).nest(Prec::Atom)),
                    })
                    .prec(Prec::App),
                Elim::Member(_, _, m) => a
                    .pretty(db)
                    .add('.', ())
                    .chain(m.pretty(db))
                    .prec(Prec::App),
                Elim::Deref => Doc::start('*')
                    .chain(a.pretty(db).nest(Prec::App))
                    .prec(Prec::App),
                Elim::Case(c, _) => c.pretty(a.pretty(db), db).prec(Prec::Term),
            },
            Expr::Fun(clos) => clos.pretty(db),
            Expr::Lit(l) => l.pretty(db).style(Doc::style_literal()),
            Expr::Pair(a, b, _) => a
                .pretty(db)
                .add(',', ())
                .space()
                .chain(b.pretty(db).nest(Prec::Pair))
                .prec(Prec::Pair),
            Expr::Struct(def, fields, _) => {
                let edef = db.def_elab(*def).unwrap().result.unwrap();
                let fnames = match edef.body {
                    DefBody::Struct(f) => f,
                    _ => unreachable!(),
                };
                edef.name
                    .pretty(db)
                    .space()
                    .add("struct", Doc::style_keyword())
                    .hardline()
                    .chain(Doc::intersperse(
                        fields.iter().zip(fnames).map(|(val, (name, _))| {
                            name.pretty(db).add(':', ()).space().chain(val.pretty(db))
                        }),
                        Doc::none().hardline(),
                    ))
                    .indent()
                    .prec(Prec::Term)
            }
            Expr::Error => Doc::none().add("%error", Doc::style_literal()),
        }
    }
}
impl Pretty for EClos {
    fn pretty(&self, db: &(impl Elaborator + ?Sized)) -> Doc {
        let EClos {
            class,
            params,
            body,
        } = self;
        let d_params = match class {
            Pi(Impl, _) | Lam(Impl, _) => Doc::start('[')
                .chain(Doc::intersperse(
                    params.iter().map(|x| {
                        x.name
                            .pretty(db)
                            .add(':', ())
                            .space()
                            .chain(x.ty.pretty(db).nest(Prec::App))
                    }),
                    Doc::start(',').space(),
                ))
                .add(']', ()),
            Lam(Expl, _) => Doc::start('(')
                .chain(Doc::intersperse(
                    params.iter().map(|x| {
                        x.name
                            .pretty(db)
                            .add(':', ())
                            .space()
                            .chain(x.ty.pretty(db).nest(Prec::App))
                    }),
                    Doc::start(',').space(),
                ))
                .add(')', ()),
            Sigma | Pi(Expl, _) if params.len() == 1 => {
                assert_eq!(params.len(), 1);
                let x = &params[0];
                pretty_bind(x.name, x.ty.pretty(db).nest(Prec::App), db, *class != Sigma)
            }
            Pi(Expl, _) => Doc::start('(')
                .chain(Doc::intersperse(
                    params
                        .iter()
                        .map(|x| pretty_bind(x.name, x.ty.pretty(db).nest(Prec::App), db, false)),
                    Doc::start(',').space(),
                ))
                .add(')', ()),
            Sigma => unreachable!("params.len(): {}", params.len()),
        };
        match class {
            Sigma => {
                assert_eq!(params.len(), 1);
                d_params
                    .add(',', ())
                    .space()
                    .chain(body.pretty(db).nest(Prec::Pair))
                    .prec(Prec::Pair)
            }
            Lam(_, _) => d_params
                .space()
                .add("=>", ())
                .space()
                .chain(body.pretty(db))
                .prec(Prec::Term),
            Pi(_, c) => d_params
                .space()
                .chain(match c {
                    CopyClass::Move => Doc::none(),
                    CopyClass::Copy => Doc::start('&'),
                    CopyClass::Mut => Doc::start('&').add("mut", Doc::style_keyword()).space(),
                })
                .add("->", ())
                .space()
                .chain(body.pretty(db).nest(Prec::Pi))
                .prec(Prec::Pi),
        }
    }
}
