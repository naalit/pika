use super::*;

pub trait AstNode: Sized {
    fn cast(syntax: SyntaxNode) -> Option<Self>;
    fn syntax(&self) -> &SyntaxNode;
    fn span(&self) -> RelSpan {
        // If possible, don't include surrounding whitespace in the span
        let start = self
            .syntax()
            .children_with_tokens()
            .find(|x| x.as_token().map_or(true, |x| !x.kind().is_trivia()))
            .map(|x| x.text_range().start());
        let end = self
            .syntax()
            .children_with_tokens()
            .filter(|x| x.as_token().map_or(true, |x| !x.kind().is_trivia()))
            .map(|x| x.text_range().end())
            .last();
        if start.is_none() || end.is_none() {
            self.syntax().text_range().into()
        } else {
            start.unwrap().into()..end.unwrap().into()
        }
    }
}

macro_rules! _make_getter {
    ($name:ident: (!$ty:ident)) => {
        #[allow(unused)]
        pub fn $name(&self) -> Option<SyntaxToken> {
            self.syntax
                .children_with_tokens()
                .filter_map(|x| x.as_token().cloned())
                .find(|x| x.kind() == SyntaxKind::$ty)
        }
    };
    ($name:ident: ($n:literal $ty:ty)) => {
        #[allow(unused)]
        pub fn $name(&self) -> Option<$ty> {
            self.syntax.children().filter_map(<$ty>::cast).nth($n)
        }
    };
    ($name:ident: [$ty:ty]) => {
        #[allow(unused)]
        pub fn $name(&self) -> Vec<$ty> {
            self.syntax.children().filter_map(<$ty>::cast).collect()
        }
    };
    ($name:ident: $ty:ty) => {
        #[allow(unused)]
        pub fn $name(&self) -> Option<$ty> {
            self.syntax.children().find_map(<$ty>::cast)
        }
    };
}
/// Syntax examples:
/// ```rust norun
/// make_nodes! {
///     // Simple nodes that correspond to one token and don't have arguments
///     Literal = ;
///     OpKind = ;
///     Name = ;
///
///     // Most nodes have arguments, which look like this
///     // `(1 Expr)` is required since there's more than one argument of the same type; this is Expr argument number 1 (starting at 0)
///     // (macro_rules! can't figure that out itself)
///     BinOp = lhs: Expr, op: OpKind, rhs: (1 Expr);
///
///     // `[Expr]` allows multiple arguments
///     Call = fun: Name, args: [Expr];
///
///     // `Expr` isn't actually its own `SyntaxKind`, just an enum that can hold one of these nodes
///     enum Expr = Literal, BinOp, Name;
/// }
/// ```
macro_rules! make_nodes {
    {enum $n:ident = $($variant:ident),*; $($rest:tt)*} => {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        pub enum $n {
            $($variant($variant),)*
        }
        impl AstNode for $n {
            fn cast(syntax: SyntaxNode) -> Option<Self> {
                $(
                    if let Some(x) = <$variant>::cast(syntax.clone()) {
                        return Some(Self::$variant(x));
                    }
                )*
                None
            }

            fn syntax(&self) -> &SyntaxNode {
                match self {
                    $(
                        Self::$variant(n) => n.syntax(),
                    )*
                }
            }
        }

        make_nodes!{ $($rest)* }
    };
    {$n:ident = $($param:ident: $param_ty:tt),*; $($rest:tt)*} => {
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        pub struct $n {
            pub syntax: SyntaxNode,
        }
        impl $n {
            $(
                _make_getter!{$param: $param_ty}
            )*
        }
        impl AstNode for $n {
            fn cast(syntax: SyntaxNode) -> Option<Self> {
                if syntax.kind() == SyntaxKind::$n {
                    Some(Self {
                        syntax,
                    })
                } else {
                    None
                }
            }

            fn syntax(&self) -> &SyntaxNode {
                &self.syntax
            }
        }

        make_nodes!{ $($rest)* }
    };
    {} => {};
}

make_nodes! {
    // Expressions
    Type = kw: (!TypeTypeKw);
    Var = name_tok: (!Name);


    Pat = expr: Expr;
    PatPar = pat: Pat;
    TermPar = expr: Expr;
    Binder = pat: Pat, ty: Ty;
    Pair = lhs: Expr, rhs: (1 Expr);

    ImpPar = par: PatPar;
    ImpPars = pars: [ImpPar];
    ImpArg = expr: Expr;
    ImpArgs = args: [ImpArg];

    WithClause = effs: [Expr];
    Lam = imp_par: ImpPars, exp_par: PatPar, body: Body;
    Pi = imp_par: ImpPars, exp_par: TermPar, body: Body, with: WithClause;

    StructInit = lhs: Expr, fields: StructFields;

    Member = var: Var;
    App = lhs: Expr, member: Member, imp: ImpArgs, exp: (1 Expr);

    Do = block: [Stmt];

    Hole = ;

    CaseKw = ;
    CatchKw = ;
    enum CaseTy = CaseKw, CatchKw;
    CaseBranch = pat: Expr, body: Body;
    Case = ty: CaseTy, scrutinee: Expr, branches: [CaseBranch];

    Lit = float: (!FloatLit), int: (!IntLit), string: (!StringLit);

    BinOpKind = ;
    BinOp = a: Expr, op: BinOpKind, b: (1 Expr);

    If = cond: Expr, a: (1 Expr), b: (2 Expr);

    // examine keyword to tell whether it's `box` or `unbox`
    // ??? TODO what do we include as the token argument
    Box = expr: Expr;

    GroupedExpr = expr: Expr;

    enum Expr =
        Var,
        Lam,
        Pi,
        App,
        Do,
        Hole,
        Case,
        Lit,
        BinOp,
        If,
        Box,
        Type,
        GroupedExpr,
        Pair,
        // Patterns parse as expressions
        EffPat,
        Binder,
        StructInit
        ;

    // synonyms for Expr to use in certain contexts
    Ty = expr: Expr;
    Body = expr: Expr;

    // Patterns
    EffPat = a: Expr, b: (1 Expr);

    // Definitions
    LetDef = pat: Pat, body: Body;
    FunDef = name: Var, imp_par: ImpPars, exp_par: PatPar, ret_ty: Ty, with: WithClause, body: Body;
    ConsDef = name: Var, imp_par: ImpPars, exp_par: TermPar, ret_ty: Ty;
    TypeDef = name: Var, imp_par: ImpPars, exp_par: PatPar, cons: [ConsDef], block: BlockDef;
    TypeDefShort = name: Var, imp_par: ImpPars, exp_par: PatPar, inner: Ty, block: BlockDef;
    TypeDefStruct = name: Var, imp_par: ImpPars, exp_par: PatPar, fields: StructFields, block: BlockDef;
    StructFields = defs: [Def];
    BlockDef = defs: [Def];

    enum Def = LetDef, FunDef, TypeDef, TypeDefShort, TypeDefStruct;

    enum Stmt = Expr, Def;

    Root = def: Def;
}

impl Var {
    pub fn name<T: Parser + ?Sized>(&self, db: &T) -> Name {
        db.name(self.name_tok().unwrap().text().to_string())
    }
}

pub trait Pretty {
    fn pretty(&self) -> Doc;
}
impl<T: Pretty> Pretty for Option<T> {
    fn pretty(&self) -> Doc {
        match self {
            Some(x) => x.pretty(),
            None => Doc::start("?"),
        }
    }
}

impl Pretty for Root {
    fn pretty(&self) -> Doc {
        self.def().pretty()
    }
}

impl Pretty for Var {
    fn pretty(&self) -> Doc {
        Doc::start(
            self.name_tok()
                .map_or("?_".to_string(), |x| x.text().to_string()),
        )
    }
}

impl Pretty for Ty {
    fn pretty(&self) -> Doc {
        self.expr().pretty()
    }
}
impl Pretty for Body {
    fn pretty(&self) -> Doc {
        self.expr().pretty()
    }
}

impl Pretty for TermPar {
    fn pretty(&self) -> Doc {
        self.expr().pretty()
    }
}
impl Pretty for PatPar {
    fn pretty(&self) -> Doc {
        self.pat().pretty()
    }
}
impl Pretty for Pat {
    fn pretty(&self) -> Doc {
        self.expr().pretty()
    }
}
impl Pretty for ImpPar {
    fn pretty(&self) -> Doc {
        Doc::start('[').chain(self.par().pretty()).add(']', ())
    }
}
impl Pretty for ImpArg {
    fn pretty(&self) -> Doc {
        Doc::start('[').chain(self.expr().pretty()).add(']', ())
    }
}
impl Pretty for ImpArgs {
    fn pretty(&self) -> Doc {
        Doc::intersperse(self.args().iter().map(|x| x.pretty()), Doc::none())
    }
}
impl Pretty for ImpPars {
    fn pretty(&self) -> Doc {
        Doc::intersperse(self.pars().iter().map(|x| x.pretty()), Doc::none())
    }
}

impl Pretty for ConsDef {
    fn pretty(&self) -> Doc {
        self.name()
            .pretty()
            .space()
            .chain(self.imp_par().pretty())
            .chain(self.exp_par().pretty())
            .add(':', ())
            .space()
            .chain(self.ret_ty().pretty())
    }
}

impl Pretty for Def {
    fn pretty(&self) -> Doc {
        match self {
            Def::LetDef(l) => Doc::none()
                .add("let", Doc::style_keyword())
                .space()
                .chain(l.pat().pretty())
                .space()
                .add('=', ())
                .space()
                .chain(l.body().pretty()),
            Def::FunDef(x) => Doc::none()
                .add("fun", Doc::style_keyword())
                .space()
                .chain(x.name().pretty())
                .space()
                .chain(x.imp_par().pretty())
                .chain(x.exp_par().pretty())
                .add(':', ())
                .space()
                .chain(x.ret_ty().pretty())
                .space()
                .add('=', ())
                .space()
                .chain(x.body().pretty()),
            Def::TypeDefShort(x) => Doc::none()
                .add("type", Doc::style_keyword())
                .space()
                .chain(x.name().pretty())
                .space()
                .chain(x.imp_par().pretty())
                .chain(x.exp_par().pretty())
                .space()
                .add("=", ())
                .space()
                .chain(x.inner().pretty())
                .chain(if let Some(block) = x.block() {
                    Doc::none().hardline().chain(
                        Doc::none()
                            .add("where", Doc::style_keyword())
                            .hardline()
                            .chain(Doc::intersperse(
                                block.defs().into_iter().map(|x| x.pretty()),
                                Doc::none().hardline(),
                            ))
                            .indent(),
                    )
                } else {
                    Doc::none()
                }),
            Def::TypeDefStruct(x) => Doc::none()
                .add("type", Doc::style_keyword())
                .space()
                .chain(x.name().pretty())
                .space()
                .chain(x.imp_par().pretty())
                .chain(x.exp_par().pretty())
                .space()
                .add("struct", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    x.fields()
                        .into_iter()
                        .flat_map(|x| x.defs())
                        .map(|x| x.pretty()),
                    Doc::none().hardline(),
                ))
                .indent()
                .chain(if let Some(block) = x.block() {
                    Doc::none().hardline().chain(
                        Doc::none()
                            .add("where", Doc::style_keyword())
                            .hardline()
                            .chain(Doc::intersperse(
                                block.defs().into_iter().map(|x| x.pretty()),
                                Doc::none().hardline(),
                            ))
                            .indent(),
                    )
                } else {
                    Doc::none()
                }),
            Def::TypeDef(x) => Doc::none()
                .add("type", Doc::style_keyword())
                .space()
                .chain(x.name().pretty())
                .space()
                .chain(x.imp_par().pretty())
                .chain(x.exp_par().pretty())
                .space()
                .add("of", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    x.cons().into_iter().map(|x| x.pretty()),
                    Doc::none().hardline(),
                ))
                .indent()
                .chain(if let Some(block) = x.block() {
                    Doc::none().hardline().chain(
                        Doc::none()
                            .add("where", Doc::style_keyword())
                            .hardline()
                            .chain(Doc::intersperse(
                                block.defs().into_iter().map(|x| x.pretty()),
                                Doc::none().hardline(),
                            ))
                            .indent(),
                    )
                } else {
                    Doc::none()
                }),
        }
    }
}

impl Pretty for Stmt {
    fn pretty(&self) -> Doc {
        match self {
            Stmt::Expr(e) => e.pretty(),
            Stmt::Def(x) => x.pretty(),
        }
    }
}

impl Pretty for BinOpKind {
    fn pretty(&self) -> Doc {
        Doc::start(self.syntax.text())
    }
}

impl Pretty for Expr {
    fn pretty(&self) -> Doc {
        let p = match self {
            Expr::Var(n) => n.pretty(),
            Expr::Type(_) => Doc::none().add("Type", Doc::style_keyword()),
            Expr::Lam(l) => Doc::none()
                .chain(l.imp_par().pretty())
                .chain(l.exp_par().pretty())
                .space()
                .add("=>", ())
                .space()
                .chain(l.body().pretty()),
            Expr::Pi(l) => Doc::none()
                .chain(l.imp_par().pretty())
                .chain(l.exp_par().pretty())
                .space()
                .add("->", ())
                .space()
                .chain(l.body().pretty()),
            Expr::StructInit(x) => x
                .lhs()
                .pretty()
                .space()
                .add("struct", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    x.fields()
                        .into_iter()
                        .flat_map(|x| x.defs())
                        .map(|x| x.pretty()),
                    Doc::none().hardline(),
                ))
                .indent(),
            Expr::App(x) => {
                if let Some(member) = x.member() {
                    let doc = x.lhs().pretty().add('.', ()).chain(member.var().pretty());
                    if x.imp().is_some() || x.exp().is_some() {
                        doc.space().chain(x.imp().pretty()).chain(x.exp().pretty())
                    } else {
                        doc
                    }
                } else {
                    x.lhs()
                        .pretty()
                        .space()
                        .chain(x.imp().pretty())
                        .chain(x.exp().pretty())
                }
            }
            Expr::Pair(x) => x
                .lhs()
                .pretty()
                .add(',', ())
                .space()
                .chain(x.rhs().pretty()),
            Expr::Binder(x) => x.pat().pretty().add(':', ()).space().chain(x.ty().pretty()),
            Expr::Do(x) => Doc::none()
                .add("do", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    x.block().into_iter().map(|x| x.pretty()),
                    Doc::none().hardline(),
                ))
                .indent(),
            Expr::Hole(_) => Doc::start("_"),
            Expr::Case(x) => Doc::none()
                .add("case", Doc::style_keyword())
                .space()
                .chain(x.scrutinee().pretty())
                .space()
                .add("of", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    x.branches().into_iter().map(|branch| {
                        branch
                            .pat()
                            .pretty()
                            .space()
                            .add("=>", ())
                            .space()
                            .chain(branch.body().pretty())
                    }),
                    Doc::none().hardline(),
                ))
                .indent(),
            Expr::Lit(l) => Doc::start(l.syntax().text()),
            Expr::BinOp(x) => x
                .a()
                .pretty()
                .space()
                .chain(x.op().pretty())
                .space()
                .chain(x.b().pretty()),
            Expr::If(x) => Doc::none()
                .add("if", Doc::style_keyword())
                .space()
                .chain(x.cond().pretty())
                .brk()
                .add("then", Doc::style_keyword())
                .space()
                .chain(x.a().pretty())
                .brk()
                .add("else", Doc::style_keyword())
                .space()
                .chain(x.b().pretty())
                .indent(),
            Expr::Box(x) => Doc::none()
                .add(
                    x.syntax()
                        .children_with_tokens()
                        .find(|x| {
                            matches!(
                                x.as_token().map(|x| x.kind()),
                                Some(SyntaxKind::BoxKw | SyntaxKind::UnboxKw)
                            )
                        })
                        .map(|x| x.as_token().unwrap().text().to_string())
                        .unwrap_or_else(|| "<box?>".to_string()),
                    Doc::style_keyword(),
                )
                .space()
                .chain(x.expr().pretty()),
            Expr::GroupedExpr(x) => return Doc::start('(').chain(x.expr().pretty()).add(')', ()),
            Expr::EffPat(x) => Doc::none()
                .add("eff", Doc::style_keyword())
                .space()
                .chain(x.a().pretty())
                .space()
                .chain(x.b().pretty()),
        };
        Doc::start('[').chain(p).add(']', ())
    }
}
