use super::*;

pub trait AstNode: Sized {
    fn cast(syntax: SyntaxNode) -> Option<Self>;
    fn syntax(&self) -> &SyntaxNode;
}

macro_rules! _make_getter {
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
macro_rules! make_nodes {
    {enum $n:ident = $($variant:ident),*; $($rest:tt)*} => {
        enum $n {
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
        struct $n {
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

make_nodes!{
    Name = ;

    // Expressions
    Type = ;
    Var = name: Name;

    ImpPar = arg: Name, ty: Ty;
    ExpPar = arg: Name, ty: Ty;
    enum Par = ImpPar, ExpPar;
    WithClause = effs: [Ty];
    Lam = par: Par, body: Body, with: WithClause;
    Pi = par: Par, ret: Ty, body: Body, with: WithClause;
    Fun = par: Ty, ret: (1 Ty), with: WithClause;

    ImpArg = expr: Expr;
    ExpArg = expr: Expr;
    enum Arg = ImpArg, ExpArg;
    App = fun: Expr, arg: Arg;

    Do = block: [Stmt];

    Hole = ;

    DotExpr = expr: Expr, dot: Name;

    CaseKw = ;
    CatchKw = ;
    enum CaseTy = CaseKw, CatchKw;
    CaseBranch = pat: Pat, body: Body;
    Case = ty: CaseTy, scrutinee: Expr, branches: [CaseBranch];

    FloatLit = ;
    IntLit = ;
    StringLit = ;
    enum Lit = FloatLit, IntLit, StringLit;

    Unit = ;

    BinOpKind = ;
    BinOp = a: Expr, op: BinOpKind, b: (1 Expr);

    If = cond: Expr, a: (1 Expr), b: (2 Expr);

    Box = expr: Expr;

    enum Expr = Var, Lam, Pi, App, Do, Hole, DotExpr, Case, Lit, Unit, BinOp, If, Box;

    // synonyms for Expr to use in certain contexts
    Ty = expr: Expr;
    Body = expr: Expr;

    // Patterns
    OrPat = a: Expr, b: (1 Expr);
    EffPat = a: Expr, b: (1 Expr);
    enum Pat = Var, App, OrPat, EffPat;

    // Statements
    LetStmt = pat: Pat, ty: Ty, body: Body;

    enum Stmt = Expr, LetStmt;
}