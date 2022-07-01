use super::*;

impl EClos {
    pub fn find_span(&self, span: RelSpan, cxt: &mut Cxt) -> Result<(), (&Expr, RelSpan)> {
        cxt.push();
        for i in &self.params {
            i.ty.find_span(span.clone(), cxt)?;
            cxt.define_local(i.name, i.ty.clone().eval(&mut cxt.env()), None);
        }
        self.body.find_span(span, cxt)?;
        cxt.pop();
        Ok(())
    }
}

impl Expr {
    pub fn find_span(&self, span: RelSpan, cxt: &mut Cxt) -> Result<(), (&Expr, RelSpan)> {
        match self {
            Expr::Type => (),
            Expr::Head(_) => (),
            Expr::Elim(a, b) => match &**b {
                Elim::App(_, x) => {
                    x.find_span(span.clone(), cxt)?;
                    a.find_span(span, cxt)?;
                }
                Elim::Member(_) => todo!(),
                Elim::Case(case, _) => {
                    a.find_span(span.clone(), cxt)?;
                    let mut r = Ok(());
                    case.visit(|x| {
                        if r.is_ok() {
                            r = x.find_span(span.clone(), cxt);
                        }
                    });
                    r?;
                }
            },
            Expr::Fun(clos) => clos.find_span(span, cxt)?,
            Expr::Lit(_) => (),
            // The type isn't a child of the pair in the source language
            Expr::Pair(a, b, _) => {
                a.find_span(span.clone(), cxt)?;
                b.find_span(span, cxt)?;
            }
            Expr::Spanned(espan, x) => {
                if espan.contains(&span.start) && espan.contains(&span.end) {
                    x.find_span(span, cxt)?;
                    return Err((&*x, espan.clone()));
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
    let mut cxt = Cxt::new(db, def_cxt);
    // Look in both the body and the type
    let (expr, span) = match def.result.as_ref()?.body.find_span(pos..pos, &mut cxt) {
        Ok(()) => def
            .result
            .as_ref()?
            .ty
            .find_span(pos..pos, &mut cxt)
            .err()?,
        Err(e) => e,
    };
    let ty = expr.ty(&mut cxt).quote(cxt.size(), Some(&cxt.mcxt));
    Some((ty.pretty(db), span))
}
