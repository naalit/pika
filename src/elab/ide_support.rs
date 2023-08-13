use super::*;

pub enum FindSpanResult<'a> {
    Name(SName, Cow<'a, Expr>),
    Expr(Cow<'a, Expr>, RelSpan),
}
impl FindSpanResult<'_> {
    fn into_owned(self) -> FindSpanResult<'static> {
        match self {
            FindSpanResult::Name(n, c) => FindSpanResult::Name(n, Cow::Owned(c.into_owned())),
            FindSpanResult::Expr(c, s) => FindSpanResult::Expr(Cow::Owned(c.into_owned()), s),
        }
    }
}

impl EClos {
    pub fn find_span(&self, span: RelSpan, cxt: &mut Cxt) -> Result<(), FindSpanResult> {
        cxt.push();
        for i in &self.params {
            i.ty.find_span(span, cxt)?;
            if i.name.1.superset(span) {
                return Err(FindSpanResult::Name(i.name, Cow::Borrowed(&i.ty)));
            }
            cxt.define_local(i.name, i.ty.clone().eval(&mut cxt.env()), None, Vec::new());
        }
        self.body.find_span(span, cxt)?;
        cxt.pop();
        Ok(())
    }
}

impl Expr {
    pub fn find_span(&self, span: RelSpan, cxt: &mut Cxt) -> Result<(), FindSpanResult> {
        match self {
            Expr::Type => (),
            &Expr::Head(Head::Var(Var::Local(n @ (_, s), _) | Var::Def(n @ (_, s), _))) => {
                if s.superset(span) {
                    eprintln!("here");
                    return Err(FindSpanResult::Name(
                        n,
                        Cow::Owned(self.ty(cxt).quote(cxt.size(), Some(&cxt.mcxt))),
                    ));
                }
            }
            Expr::Head(_) => (),
            Expr::Elim(a, b) => match &**b {
                Elim::App(_, x) => {
                    x.find_span(span, cxt)?;
                    a.find_span(span, cxt)?;
                }
                Elim::Member(_) => todo!(),
                Elim::Case(case, _) => {
                    a.find_span(span, cxt)?;
                    let mut r = Ok(());
                    case.visit(|x| {
                        if r.is_ok() {
                            r = x.find_span(span, cxt);
                        }
                    });
                    r?;
                }
            },
            Expr::Fun(clos) => clos.find_span(span, cxt)?,
            Expr::Lit(_) => (),
            // The type isn't a child of the pair in the source language
            Expr::Pair(a, b, _) => {
                a.find_span(span, cxt)?;
                b.find_span(span, cxt)?;
            }
            Expr::Ref(x) => x.find_span(span, cxt)?,
            Expr::Spanned(espan, x) => {
                if espan.superset(span) {
                    x.find_span(span, cxt)?;
                    return Err(FindSpanResult::Expr(Cow::Borrowed(&*x), *espan));
                }
            }
            Expr::Error => (),
        }
        Ok(())
    }
}

pub fn def_hover_type(db: &dyn Elaborator, def_id: Def, pos: u32) -> Option<(Doc, RelSpan)> {
    let (_, def_cxt) = db.lookup_def_node(db.to_def_node(def_id)?);
    let def = db.def_elab(def_id)?;
    // First try the def name
    let mut result = None;
    if let Some(name) = def.result.as_ref().map(|x| x.name) {
        if name.1.contains(pos) {
            result = Some(FindSpanResult::Name(
                name,
                Cow::Borrowed(&*def.result.as_ref().unwrap().ty),
            ))
        }
    };
    let mut cxt = Cxt::new(db, def_cxt);
    // Look in both the body and the type
    if result.is_none() {
        let res = match &def.result.as_ref()?.body {
            DefBody::Let(body) => body.find_span(RelSpan::new(pos, pos), &mut cxt),
            DefBody::Type(ctors) => {
                let mut res = Ok(());
                for (split, span, ty) in ctors {
                    let ty = ty.clone().quote(cxt.size(), None);
                    if span.contains(pos) {
                        res = Err(FindSpanResult::Name(
                            (split.name().unwrap(), *span),
                            Cow::Owned(ty),
                        ));
                        break;
                    }
                    let e = ty
                        .find_span(RelSpan::new(pos, pos), &mut cxt)
                        .map_err(|e| e.into_owned());
                    if e.is_err() {
                        res = e;
                        break;
                    }
                }
                res
            }
        };
        result = match res {
            Ok(()) => def
                .result
                .as_ref()?
                .ty
                .find_span(RelSpan::new(pos, pos), &mut cxt)
                .err(),
            Err(e) => Some(e),
        };
        if result.is_none() {
            for (split, _) in &def.result.as_ref()?.children {
                let res = def_hover_type(db, db.def(DefLoc::Child(def_id, *split)), pos);
                if res.is_some() {
                    return res;
                }
            }
        }
    }
    match result? {
        FindSpanResult::Name((name, span), ty) => Some((
            name.pretty(db).add(':', ()).space().chain(ty.pretty(db)),
            span,
        )),
        FindSpanResult::Expr(expr, span) => {
            let ty = expr.ty(&mut cxt).quote(cxt.size(), Some(&cxt.mcxt));
            Some((ty.pretty(db), span))
        }
    }
}

pub fn hover_type(
    db: &dyn Elaborator,
    file: File,
    split: SplitId,
    pos: u32,
) -> Option<(Doc, RelSpan)> {
    let def_id = db.def(DefLoc::Root(file, split));
    def_hover_type(db, def_id, pos)
}
