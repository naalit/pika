use super::*;

pub trait AstNode: Sized {
    fn cast(syntax: SyntaxNode) -> Option<Self>;
    fn syntax(&self) -> &SyntaxNode;
}

macro_rules! _make_getter {
    ($name:ident: (!$ty:ident)) => {
        #[allow(unused)]
        fn $name(&self) -> Option<SyntaxToken> {
            self.syntax
                .children_with_tokens()
                .filter_map(|x| x.as_token().cloned())
                .find(|x| x.kind() == SyntaxKind::$ty)
        }
    };
    ($name:ident: ($n:literal $ty:ty)) => {
        #[allow(unused)]
        fn $name(&self) -> Option<$ty> {
            self.syntax.children().filter_map(<$ty>::cast).nth($n)
        }
    };
    ($name:ident: [$ty:ty]) => {
        #[allow(unused)]
        fn $name(&self) -> Vec<$ty> {
            self.syntax.children().filter_map(<$ty>::cast).collect()
        }
    };
    ($name:ident: $ty:ty) => {
        #[allow(unused)]
        fn $name(&self) -> Option<$ty> {
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
    Type = ;
    Var = name: (!Name);

    ImpArg = expr: Expr;

    ImpPar = arg: Var, ty: Ty;
    ExpPar = arg: Var, ty: Ty;
    enum Par = Var, ImpArg, ImpPar, ExpPar;
    WithClause = effs: [Expr];
    Lam = params: [Par], body: Body;
    Pi = params: [Par], body: Body, with: WithClause;
    Fun = param: Expr, ret: (1 Expr), with: WithClause;

    enum AppArg = Expr, ImpArg;
    AppList = exprs: [AppArg];

    Do = block: [Stmt];

    Hole = ;

    DotExpr = expr: Expr, member: Var;

    CaseKw = ;
    CatchKw = ;
    enum CaseTy = CaseKw, CatchKw;
    CaseBranch = pat: Expr, body: Body;
    Case = ty: CaseTy, scrutinee: Expr, branches: [CaseBranch];

    Lit = float: (!FloatLit), int: (!IntLit), string: (!StringLit);

    Unit = ;

    BinOpKind = ;
    BinOp = a: Expr, op: BinOpKind, b: (1 Expr);

    If = cond: Expr, a: (1 Expr), b: (2 Expr);

    // examine keyword to tell whether it's `box` or `unbox`
    // ??? TODO what do we include as the token argument
    Box = expr: Expr;

    GroupedExpr = expr: Expr;

    Member = expr: Expr, name: Var;

    enum Expr =
        Var,
        Lam,
        Pi,
        AppList,
        Do,
        Hole,
        DotExpr,
        Case,
        Lit,
        Unit,
        BinOp,
        If,
        Box,
        GroupedExpr,
        Member,
        // Patterns parse as expressions
        OrPat,
        EffPat
        ;

    // synonyms for Expr to use in certain contexts
    Ty = expr: Expr;
    Body = expr: Expr;

    // Patterns
    OrPat = a: Expr, b: (1 Expr);
    EffPat = a: Expr, b: (1 Expr);

    // Statements
    LetStmt = pat: Expr, ty: Ty, body: Body;

    enum Stmt = Expr, LetStmt;

    Root = expr: Expr;
}

use crate::pretty::Prec;

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
        match self.expr() {
            Some(e) => e.pretty(),
            None => Doc::start("<NO EXPRESSION>"),
        }
    }
}

impl Pretty for Var {
    fn pretty(&self) -> Doc {
        Doc::start(
            self.name()
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

impl Pretty for Par {
    fn pretty(&self) -> Doc {
        match self {
            Par::Var(n) => n.pretty(),
            Par::ImpArg(i) => Doc::start('[')
                .chain(i.expr().pretty())
                .add(']', ())
                .prec(Prec::Atom),
            Par::ImpPar(i) => Doc::start('[')
                .chain(i.arg().pretty())
                .add(':', ())
                .chain(i.ty().pretty())
                .add(']', ())
                .prec(Prec::Atom),
            Par::ExpPar(i) => Doc::start('(')
                .chain(i.arg().pretty())
                .add(':', ())
                .chain(i.ty().pretty())
                .add(')', ())
                .prec(Prec::Atom),
        }
    }
}

impl Pretty for AppArg {
    fn pretty(&self) -> Doc {
        match self {
            AppArg::Expr(e) => e.pretty(),
            AppArg::ImpArg(i) => Doc::start('[')
                .chain(i.expr().pretty())
                .add(']', ())
                .prec(Prec::Atom),
        }
    }
}

impl Pretty for Stmt {
    fn pretty(&self) -> Doc {
        match self {
            Stmt::Expr(e) => e.pretty(),
            Stmt::LetStmt(l) => Doc::none()
                .add("let", Doc::style_keyword())
                .space()
                .chain(l.pat().pretty())
                .add(':', ())
                .chain(l.ty().pretty())
                .space()
                .add('=', ())
                .space()
                .chain(l.body().pretty()),
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
            Expr::Lam(l) => Doc::intersperse(
                l.params().into_iter().map(|x| x.pretty()),
                Doc::none().space(),
            )
            .space()
            .add("=>", ())
            .chain(l.body().pretty()),
            Expr::Pi(l) => Doc::intersperse(
                l.params().into_iter().map(|x| x.pretty()),
                Doc::none().space(),
            )
            .space()
            .add("->", ())
            .chain(l.body().pretty()),
            Expr::AppList(x) => Doc::intersperse(
                x.exprs().into_iter().map(|x| x.pretty()),
                Doc::none().space(),
            ),
            Expr::Do(x) => Doc::none()
                .add("do", Doc::style_keyword())
                .hardline()
                .chain(Doc::intersperse(
                    x.block().into_iter().map(|x| x.pretty()),
                    Doc::none().hardline(),
                ))
                .indent(),
            Expr::Hole(_) => Doc::start("_"),
            Expr::DotExpr(x) => x.expr().pretty().add('.', ()).chain(x.member().pretty()),
            Expr::Case(x) => Doc::none()
                .add("case", Doc::style_keyword())
                .space()
                .chain(x.scrutinee().pretty())
                .space()
                .add("of", Doc::style_keyword())
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
            Expr::Unit(_) => Doc::start("()"),
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
            Expr::GroupedExpr(x) => Doc::start('(').chain(x.expr().pretty()).add(')', ()),
            Expr::Member(x) => x.expr().pretty().add('.', ()).chain(x.name().pretty()),
            Expr::OrPat(x) => x.a().pretty().add('|', ()).chain(x.b().pretty()),
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
