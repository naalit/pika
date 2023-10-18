use super::*;

pub trait AstNode: Sized {
    fn cast(syntax: SyntaxNode) -> Option<Self>;
    fn syntax(&self) -> Option<&SyntaxNode>;
    fn span(&self) -> RelSpan;
}

pub fn node_span(node: &SyntaxNode) -> RelSpan {
    // If possible, don't include surrounding whitespace in the span
    let start = node
        .children_with_tokens()
        .find(|x| x.as_token().map_or(true, |x| !x.kind().is_trivia()))
        .map(|x| match x {
            rowan::NodeOrToken::Node(n) => node_span(&n).start,
            rowan::NodeOrToken::Token(t) => t.text_range().start().into(),
        });
    let end = node
        .children_with_tokens()
        .filter(|x| x.as_token().map_or(true, |x| !x.kind().is_trivia()))
        .last()
        .map(|x| match x {
            rowan::NodeOrToken::Node(n) => node_span(&n).end,
            rowan::NodeOrToken::Token(t) => t.text_range().end().into(),
        });
    if start.is_none() || end.is_none() {
        node.text_range().into()
    } else {
        RelSpan::new(start.unwrap().into(), end.unwrap().into())
    }
}

macro_rules! _make_ty {
    ((!$ty:ident)) => {
        Option<SyntaxToken>
    };
    (($n:literal $ty:ty)) => {
        Option<std::boxed::Box<$ty>>
    };
    ([$ty:ty]) => {
        Vec<$ty>
    };
    ($ty:ty) => {
        Option<std::boxed::Box<$ty>>
    };
}
macro_rules! _make_getter {
    ($name:ident: (!$ty:ident)) => {
        #[allow(unused)]
        pub fn $name(&self) -> Option<SyntaxToken> {
            match self {
                Self::Node(s) => s
                    .children_with_tokens()
                    .filter_map(|x| x.as_token().cloned())
                    .find(|x| x.kind() == SyntaxKind::$ty),
                Self::Val { $name, .. } => $name.clone(),
            }
        }
    };
    ($name:ident: ($n:literal $ty:ty)) => {
        #[allow(unused)]
        pub fn $name(&self) -> Option<$ty> {
            match self {
                Self::Node(s) => s.children().filter_map(<$ty>::cast).nth($n),
                Self::Val { $name, .. } => $name.as_ref().map(|x| (**x).clone()),
            }
        }
    };
    ($name:ident: [$ty:ty]) => {
        #[allow(unused)]
        pub fn $name(&self) -> Vec<$ty> {
            match self {
                Self::Node(s) => s.children().filter_map(<$ty>::cast).collect(),
                Self::Val { $name, .. } => $name.clone(),
            }
        }
    };
    ($name:ident: $ty:ty) => {
        #[allow(unused)]
        pub fn $name(&self) -> Option<$ty> {
            match self {
                Self::Node(s) => s.children().find_map(<$ty>::cast),
                Self::Val { $name, .. } => $name.as_ref().map(|x| (**x).clone()),
            }
        }
    };
}
/// Syntax examples:
/// ```rust ignore
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

            fn syntax(&self) -> Option<&SyntaxNode> {
                match self {
                    $(
                        Self::$variant(n) => n.syntax(),
                    )*
                }
            }

            fn span(&self) -> RelSpan {
                match self {
                    $(
                        Self::$variant(n) => n.span(),
                    )*
                }
            }
        }

        make_nodes!{ $($rest)* }
    };
    {$n:ident = $($param:ident: $param_ty:tt),*; $($rest:tt)*} => {
        #[allow(unused)]
        #[derive(Clone, Debug, PartialEq, Eq, Hash)]
        pub enum $n {
            Node(SyntaxNode),
            Val {
                span: RelSpan,
                $(
                    $param: _make_ty!($param_ty),
                )*
            }
        }
        impl $n {
            $(
                _make_getter!{$param: $param_ty}
            )*
        }
        impl AstNode for $n {
            fn cast(syntax: SyntaxNode) -> Option<Self> {
                if syntax.kind() == SyntaxKind::$n {
                    Some(Self::Node(syntax))
                } else {
                    None
                }
            }

            fn syntax(&self) -> Option<&SyntaxNode> {
                match self {
                    Self::Node(s) => Some(s),
                    _ => None,
                }
            }

            fn span(&self) -> RelSpan {
                match self {
                    Self::Node(s) => node_span(s),
                    Self::Val { span, .. } => *span,
                }
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
    Binder = pat: Pat, ty: Ty;
    Pair = lhs: Expr, rhs: (1 Expr);

    ExpPar = expr: Expr;
    ImpPar = expr: Expr;
    FunPars = imp: ImpPar, exp: ExpPar;
    PiPars = imp: ImpPar, exp: ExpPar;
    TypePars = imp: ImpPar, exp: ExpPar;
    ImplPars = imp: ImpPar;

    ImpArg = expr: Expr;
    ImpArgs = args: [ImpArg];

    WithClause = effs: [Expr];
    Lam = pars: FunPars, body: Body;
    Pi = pars: PiPars, class: FunClass, body: Body, with: WithClause;
    CapTok = mutkw: (!MutKw), immkw: (!ImmKw), ownkw: (!OwnKw);
    FunClass = cap: CapTok;

    StructInit = lhs: Expr, fields: StructFields;

    Member = var: Var;
    App = lhs: Expr, member: Member, imp: ImpArgs, exp: (1 Expr), do_expr: AppDo;

    Do = block: [Stmt];
    AppDo = expr: Expr;

    MatchKw = ;
    CatchKw = ;
    enum CaseTy = MatchKw, CatchKw;
    CaseBranch = pat: Expr, body: Body;
    Match = ty: CaseTy, scrutinee: Expr, branches: [CaseBranch];

    Lit = float: (!FloatLit), int: (!IntLit), string: (!StringLit);

    BinOpKind = ;
    BinOp = a: Expr, op: BinOpKind, b: (1 Expr);

    If = cond: Expr, a: (1 Expr), b: (2 Expr);

    // examine keyword to tell whether it's `box` or `unbox`
    // ??? TODO what do we include as the token argument
    Box = expr: Expr;

    Cap = captok: CapTok, expr: Expr;
    Ref = expr: Expr;
    Assign = lhs: Expr, rhs: (1 Expr);
    ImplPat = expr: Expr;

    GroupedExpr = expr: Expr;

    enum Expr =
        Var,
        Lam,
        Pi,
        App,
        Do,
        Match,
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
        StructInit,
        Cap,
        Ref,
        Assign,
        ImplPat
        ;

    // synonyms for Expr to use in certain contexts
    Ty = expr: Expr;
    Body = expr: Expr;

    // Patterns
    EffPat = a: Expr, b: (1 Expr);

    // Definitions
    LetDef = pat: Pat, body: Body;
    FunDef = name: Var, pars: FunPars, ret_ty: Ty, with: WithClause, body: Body;
    ConsDef = name: Var, pars: TypePars, ret_ty: Ty;
    TypeDef = name: Var, pars: TypePars, body: TypeDefBody, block: BlockDef;
    ImplDef = pars: ImplPars, name: Var, body: Body;
    enum TypeDefBody = TypeDefStruct, TypeDefCtors;
    TypeDefCtors = cons: [ConsDef];
    TypeDefStruct = fields: StructFields;
    StructFields = fields: [Stmt];
    BlockDef = defs: [Def];

    enum Def = LetDef, FunDef, TypeDef, ImplDef;

    enum Stmt = Expr, Def;

    Root = def: Def;
}

impl Root {
    pub fn print_tree(&self) {
        print_tree(self.syntax().unwrap(), 0)
    }
}
fn print_tree(node: &SyntaxNode, indent: usize) {
    for _ in 0..indent {
        print!(" ");
    }
    println!("{:?}", node);
    for i in node.children_with_tokens() {
        match i {
            rowan::NodeOrToken::Node(n) => print_tree(&n, indent + 2),
            rowan::NodeOrToken::Token(t) => {
                for _ in 0..indent + 2 {
                    print!(" ");
                }
                println!("{:?}", t);
            }
        }
    }
}

impl Var {
    pub fn name<T: Parser + ?Sized>(&self, db: &T) -> SName {
        (
            db.name(self.name_tok().unwrap().text().to_string()),
            self.span(),
        )
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

impl Pretty for Pat {
    fn pretty(&self) -> Doc {
        self.expr().pretty()
    }
}
impl Pretty for ImpPar {
    fn pretty(&self) -> Doc {
        Doc::start('[').chain(self.expr().pretty()).add(']', ())
    }
}
impl Pretty for ExpPar {
    fn pretty(&self) -> Doc {
        Doc::start('(').chain(self.expr().pretty()).add(')', ())
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

impl Pretty for FunPars {
    fn pretty(&self) -> Doc {
        self.imp().pretty().chain(self.exp().pretty())
    }
}
impl Pretty for PiPars {
    fn pretty(&self) -> Doc {
        self.imp().pretty().chain(self.exp().pretty())
    }
}
impl Pretty for TypePars {
    fn pretty(&self) -> Doc {
        self.imp().pretty().chain(self.exp().pretty())
    }
}
impl Pretty for ImplPars {
    fn pretty(&self) -> Doc {
        self.imp().pretty()
    }
}

impl Pretty for ConsDef {
    fn pretty(&self) -> Doc {
        self.name()
            .pretty()
            .chain(self.pars().pretty())
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
                .chain(x.pars().pretty())
                .add(':', ())
                .space()
                .chain(x.ret_ty().pretty())
                .space()
                .add('=', ())
                .space()
                .chain(x.body().pretty()),
            Def::TypeDef(x) => Doc::none()
                .add("type", Doc::style_keyword())
                .space()
                .chain(x.name().pretty())
                .space()
                .chain(x.pars().pretty())
                .space()
                .chain(match x.body() {
                    None => Doc::none(),
                    Some(TypeDefBody::TypeDefStruct(x)) => Doc::none()
                        .add("struct", Doc::style_keyword())
                        .hardline()
                        .chain(Doc::intersperse(
                            x.fields()
                                .into_iter()
                                .flat_map(|x| x.fields())
                                .map(|x| x.pretty()),
                            Doc::none().hardline(),
                        ))
                        .indent(),
                    Some(TypeDefBody::TypeDefCtors(x)) => Doc::none()
                        .add("of", Doc::style_keyword())
                        .hardline()
                        .chain(Doc::intersperse(
                            x.cons().into_iter().map(|x| x.pretty()),
                            Doc::none().hardline(),
                        ))
                        .indent(),
                })
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
            Def::ImplDef(x) => Doc::none()
                .add("impl", Doc::style_keyword())
                .chain(x.pars().pretty())
                .space()
                .chain(x.name().pretty())
                .add(": ", ())
                .chain(x.body().pretty()),
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
        Doc::start(self.syntax().unwrap().text())
    }
}

impl Pretty for CapTok {
    fn pretty(&self) -> Doc {
        Doc::start(if self.immkw().is_some() {
            "imm"
        } else if self.mutkw().is_some() {
            "mut"
        } else if self.ownkw().is_some() {
            "own"
        } else {
            "<unknown cap>"
        })
        .style(Doc::style_keyword())
    }
}

impl Pretty for Expr {
    fn pretty(&self) -> Doc {
        let p = match self {
            Expr::Var(n) => n.pretty(),
            Expr::Type(_) => Doc::none().add("Type", Doc::style_keyword()),
            Expr::Lam(l) => Doc::none()
                .chain(l.pars().pretty())
                .space()
                .add("=>", ())
                .space()
                .chain(l.body().pretty()),
            Expr::Pi(l) => Doc::none()
                .chain(l.pars().pretty())
                .space()
                .chain(match l.class() {
                    None => Doc::none(),
                    Some(x) => x.cap().pretty(),
                })
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
                        .flat_map(|x| x.fields())
                        .map(|x| x.pretty()),
                    Doc::none().hardline(),
                ))
                .indent(),
            Expr::App(x) => if let Some(member) = x.member() {
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
            .chain(match x.do_expr() {
                Some(x) => Doc::start(" do")
                    .style(Doc::style_keyword())
                    .space()
                    .chain(x.expr().pretty()),
                None => Doc::none(),
            }),
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
            Expr::Match(x) => x
                .scrutinee()
                .pretty()
                .space()
                .add("match", Doc::style_keyword())
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
            Expr::Lit(l) => Doc::start(l.syntax().unwrap().text()),
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
                        .unwrap()
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
            Expr::ImplPat(r) => Doc::start("impl ")
                .style(Doc::style_keyword())
                .chain(r.expr().pretty()),
            Expr::Cap(r) => Doc::start("<cap> ").chain(r.expr().pretty()),
            Expr::Ref(x) => Doc::start("ref ")
                .style(Doc::style_keyword())
                .chain(x.expr().pretty()),
            Expr::Assign(x) => x.lhs().pretty().add(" = ", ()).chain(x.rhs().pretty()),
        };
        Doc::start('{').chain(p).add('}', ())
    }
}
