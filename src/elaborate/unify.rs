use super::{MCxt, TypeError};
use crate::common::*;
use crate::term::{ClosTy::*, Elim, StructKind};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct UnifyMode {
    inline: bool,
    local: bool,
}
impl UnifyMode {
    fn new(local: bool, inline: bool) -> UnifyMode {
        UnifyMode { inline, local }
    }
}

fn p_unify_elim(
    mode: UnifyMode,
    a: Elim,
    b: Elim,
    size: Size,
    span: Span,
    mcxt: &mut MCxt,
) -> Result<TBool, TypeError> {
    match (a, b) {
        (Elim::App(i, a), Elim::App(j, b)) if i == j => p_unify(mode, a, b, size, span, mcxt),

        _ => Ok(No),
    }
}

fn p_unify(
    mode: UnifyMode,
    a: Val,
    b: Val,
    size: Size,
    span: Span,
    mcxt: &mut MCxt,
) -> Result<TBool, TypeError> {
    match (a, b) {
        (Val::Arc(a), b) | (b, Val::Arc(a)) => {
            let a = a.into_owned();
            p_unify(mode, a, b, size, span, mcxt)
        }

        (Val::Type, Val::Type) => Ok(Yes),

        (Val::Lit(a, _), Val::Lit(b, _)) => Ok((a == b).into()),

        (Val::App(h, _, v, _), Val::App(h2, _, v2, _)) if h.unify(h2, mcxt.db) => {
            let mut r = Yes;
            for (a, b) in v.into_iter().zip(v2.into_iter()) {
                r = r & p_unify_elim(mode, a, b, size, span, mcxt)?;
            }
            Ok(r)
        }

        (Val::Box(_, a), b) | (b, Val::Box(_, a)) => p_unify(mode, *a, b, size, span, mcxt),

        (Val::Struct(k, v), Val::Struct(k2, mut v2)) => {
            if v.len() != v2.len() {
                return Ok(No);
            }
            match (&k, k2) {
                (StructKind::Struct(_), StructKind::Struct(_)) => (),
                (StructKind::Sig, StructKind::Sig) => (),
                _ => return Ok(No),
            }
            let before_defs = mcxt.local_defs.clone();
            let mut r = Yes;
            for (d1, n, a) in v.into_iter() {
                if let Some((i, _)) = v2.iter().enumerate().find(|(_, (_, n2, _))| *n2 == n) {
                    let (d2, _, b) = v2.remove(i);
                    r = r & p_unify(mode, a, b.clone(), size, span, mcxt)?;
                    let ty = match k {
                        StructKind::Sig => b.quote(size, mcxt),
                        StructKind::Struct(_) => b.quote(size, mcxt).ty(size, mcxt),
                    };
                    mcxt.local_defs
                        .push((d1, Term::Var(Var::Top(d2), Box::new(ty))));
                } else {
                    r = No;
                    break;
                }
            }
            mcxt.local_defs = before_defs;
            Ok(r)
        }

        // Since our terms are locally nameless (we're using De Bruijn levels), we automatically get alpha equivalence.
        (Val::Clos(Lam, _, cl, _), Val::Clos(Lam, _, cl2, _)) => p_unify(
            mode,
            cl.vquote(size, mcxt),
            cl2.vquote(size, mcxt),
            size.inc(),
            span,
            mcxt,
        ),

        // If one side is a lambda, the other side just needs to unify to the same thing when we apply it to the same thing
        (Val::Clos(Lam, icit, cl, _), t) | (t, Val::Clos(Lam, icit, cl, _)) => {
            let ty = cl.ty.clone();
            p_unify(
                mode,
                cl.vquote(size, mcxt),
                t.app(Elim::App(icit, Val::local(size.next_lvl(), ty)), mcxt),
                size.inc(),
                span,
                mcxt,
            )
        }

        (Val::Clos(Pi, i, cl, effs), Val::Clos(Pi, i2, cl2, effs2)) if i == i2 => {
            Ok(
                p_unify(mode, cl.ty.clone(), cl2.ty.clone(), size, span, mcxt)?
                // Applying both to the same thing (Local(l))
                & p_unify(
                    mode,
                    cl.vquote(size, mcxt),
                    cl2.vquote(size, mcxt),
                    size.inc(),
                    span,
                    mcxt,
                )?
                & TBool::from(effs.len() == effs2.len())
                & effs
                    .into_iter()
                    .zip(effs2)
                    .map(|(a, b)| p_unify(mode, a, b, size, span, mcxt))
                    .fold(Ok(Yes), |acc, r| acc.and_then(|acc| r.map(|r| acc & r)))?,
            )
        }
        (Val::Clos(Pi, Icit::Expl, cl, effs), Val::Fun(from, to, effs2))
        | (Val::Fun(from, to, effs), Val::Clos(Pi, Icit::Expl, cl, effs2)) => {
            Ok(p_unify(mode, cl.ty.clone(), *from, size, span, mcxt)?
                & p_unify(mode, cl.vquote(size, mcxt), *to, size.inc(), span, mcxt)?
                & TBool::from(effs.len() == effs2.len())
                & effs
                    .into_iter()
                    .zip(effs2)
                    .map(|(a, b)| p_unify(mode, a, b, size, span, mcxt))
                    .fold(Ok(Yes), |acc, r| acc.and_then(|acc| r.map(|r| acc & r)))?)
        }
        (Val::Fun(a, b, effs), Val::Fun(a2, b2, effs2)) => {
            Ok(p_unify(mode, *a, *a2, size, span, mcxt)?
                & p_unify(mode, *b, *b2, size, span, mcxt)?
                & TBool::from(effs.len() == effs2.len())
                & effs
                    .into_iter()
                    .zip(effs2)
                    .map(|(a, b)| p_unify(mode, a, b, size, span, mcxt))
                    .fold(Ok(Yes), |acc, r| acc.and_then(|acc| r.map(|r| acc & r)))?)
        }

        // Solve metas

        // Make sure order doesn't matter - switch sides if the second one is higher
        (Val::App(Var::Meta(m), mty, s, g), Val::App(Var::Meta(m2), mty2, s2, g2))
            if m2.higher_priority(m, mcxt) =>
        {
            p_unify(
                mode,
                Val::App(Var::Meta(m2), mty2, s2, g2),
                Val::App(Var::Meta(m), mty, s, g),
                size,
                span,
                mcxt,
            )
        }

        (Val::App(Var::Meta(m), _, sp, _), t) | (t, Val::App(Var::Meta(m), _, sp, _)) => {
            match mcxt.get_meta(m) {
                Some(v) => {
                    let v = sp
                        .into_iter()
                        .fold(v.evaluate(&mcxt.env(), mcxt), |f, e| f.app(e, mcxt));
                    p_unify(mode, v, t, size, span, mcxt)
                }
                None => {
                    mcxt.solve(span, m, &sp, t, size)?;
                    Ok(Yes)
                }
            }
        }

        // Solve local constraints
        // We prioritize solving the innermost local - so the one with the highest level
        (Val::App(Var::Local(m), mty, s, g), Val::App(Var::Local(m2), mty2, s2, g2))
            if mode.local
                && m2 > m
                && mcxt.local_val(m).is_none()
                && mcxt.local_val(m2).is_none() =>
        {
            p_unify(
                mode,
                Val::App(Var::Local(m2), mty2, s2, g2),
                Val::App(Var::Local(m), mty, s, g),
                size,
                span,
                mcxt,
            )
        }
        (Val::App(Var::Local(l), _, sp, _), t) | (t, Val::App(Var::Local(l), _, sp, _))
            if mode.local
                // because if it's already solved, or if the other one is a solved local, we'll handle that with the normal inlining logic down below
                && mcxt.local_val(l).is_none()
                && !matches!(t, Val::App(Var::Local(l2), _, _, _) if mcxt.local_val(l2).is_some()) =>
        {
            mcxt.solve_local(l, &sp, t)?;
            Ok(Yes)
        }

        // If the reason we can't unify is that one side is a top variable, then we can try again after inlining.
        (Val::App(Var::Top(_), _, _, _), _) | (_, Val::App(Var::Top(_), _, _, _))
            if !mode.inline =>
        {
            Ok(Maybe)
        }
        // Same with local variables with constraints
        (Val::App(Var::Local(l), _, _, _), _) | (_, Val::App(Var::Local(l), _, _, _))
            if !mode.inline && mcxt.local_val(l).is_some() =>
        {
            Ok(Maybe)
        }

        (Val::App(h, hty, sp, g), Val::App(h2, hty2, sp2, g2)) if mode.inline => {
            if let Some(v) = g.resolve(h, &sp, size, mcxt) {
                p_unify(mode, Val::App(h2, hty2, sp2, g2), v, size, span, mcxt)
            } else if let Some(v) = g2.resolve(h2, sp2, size, mcxt) {
                p_unify(mode, Val::App(h, hty, sp, g), v, size, span, mcxt)
            } else {
                Ok(No)
            }
        }

        (Val::App(h, _, sp, g), x) | (x, Val::App(h, _, sp, g)) if mode.inline => {
            if let Some(v) = g.resolve(h, sp, size, mcxt) {
                p_unify(mode, x, v, size, span, mcxt)
            } else {
                Ok(No)
            }
        }

        // If that's not the reason, then we know inlining won't help.
        _ => Ok(No),
    }
}

/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn unify(a: Val, b: Val, size: Size, span: Span, mcxt: &mut MCxt) -> Result<bool, TypeError> {
    match p_unify(
        UnifyMode::new(false, false),
        a.clone(),
        b.clone(),
        size,
        span,
        mcxt,
    )? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(UnifyMode::new(false, true), a, b, size, span, mcxt)?.not_maybe()),
    }
}

/// Like `unify()`, but finds local constraints and adds them to the context.
///
/// Note that the order of `a` and `b` doesn't matter - Pika doesn't have subtyping.
pub fn local_unify(
    a: Val,
    b: Val,
    size: Size,
    span: Span,
    mcxt: &mut MCxt,
) -> Result<bool, TypeError> {
    match p_unify(
        UnifyMode::new(true, false),
        a.clone(),
        b.clone(),
        size,
        span,
        mcxt,
    )? {
        Yes => Ok(true),
        No => Ok(false),
        Maybe => Ok(p_unify(UnifyMode::new(true, true), a, b, size, span, mcxt)?.not_maybe()),
    }
}
