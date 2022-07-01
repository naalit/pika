use super::*;

pub enum FindSpanResult<'a> {
    Name(SName, &'a Expr),
    Expr(&'a Expr, RelSpan),
}

impl EClos {
    pub fn find_span(&self, span: RelSpan, cxt: &mut Cxt) -> Result<(), FindSpanResult> {
        cxt.push();
        for i in &self.params {
            i.ty.find_span(span, cxt)?;
            if i.name.1.superset(span) {
                return Err(FindSpanResult::Name(i.name, &i.ty));
            }
            cxt.define_local(i.name, i.ty.clone().eval(&mut cxt.env()), None);
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
            Expr::Spanned(espan, x) => {
                if espan.superset(span) {
                    x.find_span(span, cxt)?;
                    return Err(FindSpanResult::Expr(&*x, *espan));
                }
            }
            Expr::Error => (),
        }
        Ok(())
    }
}

pub fn hover_type(
    db: &dyn Elaborator,
    file: File,
    split: SplitId,
    pos: u32,
) -> Option<(Doc, RelSpan)> {
    // TODO visit child defs
    let def = db.def(DefLoc::Root(file, split));
    let (_, def_cxt) = db.lookup_def_node(db.to_def_node(def)?);
    let def = db.def_elab(def)?;
    // First try the def name
    let mut result = None;
    if let Some(name) = def.result.as_ref().map(|x| x.name) {
        if name.1.contains(pos) {
            result = Some(FindSpanResult::Name(
                name,
                &*def.result.as_ref().unwrap().ty,
            ))
        }
    };
    let mut cxt = Cxt::new(db, def_cxt);
    // Look in both the body and the type
    if result.is_none() {
        result = Some(
            match def
                .result
                .as_ref()?
                .body
                .find_span(RelSpan::new(pos, pos), &mut cxt)
            {
                Ok(()) => def
                    .result
                    .as_ref()?
                    .ty
                    .find_span(RelSpan::new(pos, pos), &mut cxt)
                    .err()?,
                Err(e) => e,
            },
        );
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
