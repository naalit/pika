//! This module describes LowIR, which should be pretty close to LLVM IR, but it doesn't involve any FFI
//! The process of lowering to LowIR uses Salsa
//! In `codegen`, we use Inkwell to convert LowIR into LLVM outside of the Salsa framework

use crate::{affine::Mult, bicheck::TCtx, common::*, term::Builtin};
use lazy_static::lazy_static;
use std::ops::{Deref, DerefMut};
use std::sync::RwLock;

pub struct LCtx<'a> {
    pub low_tys: HashMap<Sym, LowTy>,
    pub ectx: ECtx<'a>,
}
impl<'a> Clone for LCtx<'a> {
    fn clone(&self) -> Self {
        LCtx {
            low_tys: self.low_tys.clone(),
            ectx: self.ectx.clone(),
        }
    }
}
impl<'a> From<ECtx<'a>> for LCtx<'a> {
    fn from(ectx: ECtx<'a>) -> Self {
        LCtx {
            low_tys: HashMap::new(),
            ectx,
        }
    }
}
impl<'a> LCtx<'a> {
    pub fn new(db: &'a (impl Scoped + HasDatabase)) -> Self {
        LCtx {
            low_tys: HashMap::new(),
            ectx: ECtx::new(db),
        }
    }

    pub fn low_ty(&self, k: Sym) -> Option<LowTy> {
        self.low_tys
            .get(&k)
            .cloned()
            .or_else(|| self.database().low_ty(self.scope(), k).ok())
    }
    pub fn set_low_ty(&mut self, k: Sym, v: LowTy) {
        self.low_tys.insert(k, v);
    }

    /// Gets the monomorphization for the given named function with the given parameter type, if one exists
    pub fn mono(&self, f: Sym, x: &Elab) -> Option<(String, LowTy)> {
        let mut tctx = TCtx::new(self);
        self.database()
            .monos()
            .get(&f)?
            .iter()
            .find(|v| {
                let (k, _, _) = &***v;
                x.unify(k, &mut tctx, &mut Vec::new())
            })
            .map(|x| (x.1.clone(), x.2.clone()))
    }

    /// Registers a monomorphization for the given named function with the given parameter type
    pub fn set_mono(&mut self, f: Sym, x: Elab, mono: String, ty: LowTy) {
        self.database()
            .monos_mut()
            .entry(f)
            .or_insert_with(Vec::new)
            .push(Arc::new((x, mono, ty)));
    }

    pub fn add_clos(&mut self, clos: &Clos) {
        let low_tys: Vec<_> = clos
            .tys
            .iter()
            .filter_map(|(k, v)| {
                if **v != Elab::Bottom && v.is_concrete(self) {
                    Some((*k, v.as_low_ty(self)))
                } else {
                    None
                }
            })
            .collect();
        self.low_tys.extend(low_tys);
        self.ectx.vals.extend(clos.vals.iter().cloned());
    }
}
impl<'a> Scoped for LCtx<'a> {
    fn scope(&self) -> ScopeId {
        self.ectx.scope()
    }
}
impl<'a> HasBindings for LCtx<'a> {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.database().bindings_ref()
    }
}
impl<'a> HasDatabase for LCtx<'a> {
    fn database(&self) -> &dyn MainGroupP {
        self.ectx.database()
    }
}
impl<'a> Deref for LCtx<'a> {
    type Target = ECtx<'a>;
    fn deref(&self) -> &ECtx<'a> {
        &self.ectx
    }
}
impl<'a> DerefMut for LCtx<'a> {
    fn deref_mut(&mut self) -> &mut ECtx<'a> {
        &mut self.ectx
    }
}

lazy_static! {
    static ref CLOSURE_NUM: RwLock<u32> = RwLock::new(0);
}
fn next_closure() -> u32 {
    let mut n = CLOSURE_NUM.write().unwrap();
    *n += 1;
    *n - 1
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd)]
pub enum FunAttr {
    AlwaysInline,
    Private,
}

/// A binary integer math operation
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum IntOp {
    Add,
    Sub,
    Mul,
    Div,
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum CompOp {
    Eq,
}

/// A binary logic operation, used for pattern matching compilation
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum BoolOp {
    And,
    Or,
}

/// A module in LowIR
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowMod {
    pub name: String,
    pub funs: Vec<LowFun>,
}

/// Top-level definitions are represented as functions in LowIR
/// This cannot take arguments, refer to LowIR::Fun for one that can
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LowFun {
    pub name: String,
    pub ret_ty: LowTy,
    pub body: LowIR,
}

use std::num::NonZeroU32;
#[derive(Clone, Debug, PartialEq, Eq, Copy, Hash)]
pub struct BlockId(NonZeroU32);
static mut BLOCKS: u32 = 0;
pub fn next_block() -> BlockId {
    unsafe {
        BLOCKS += 1;
        BlockId(NonZeroU32::new(BLOCKS).unwrap())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Phi {
    pub incoming: Vec<(BlockId, Sym)>,
    pub result: Sym,
}

/// A LowIR type
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd)]
pub enum LowTy {
    /// A n-bit integer
    Int(u32),
    /// A `void*` used for unknown closure lctxironments. LLVM doesn't have `void*`, though, so it's really an `i8*`
    VoidPtr,
    /// Pika's `()` compiles to `{}`, nothing actually returns `void`
    Unit,
    /// A borrowed closure (the lctxironment is essentially a `void*`), which you can call or pass as an argument
    ClosRef {
        from: Box<LowTy>,
        to: Box<LowTy>,
    },
    /// An owned closure (with a known lctxironment), which is mostly used for returning from functions
    ClosOwn {
        from: Box<LowTy>,
        to: Box<LowTy>,
        upvalues: Vec<LowTy>,
    },
    /// No distinction between pairs and structs like in the main language
    /// Struct fields are stored in order of raw symbol numbers, which is NOT stable across modules or recompiles
    /// It is stable within one compilation of a module, though, which is enough for now
    Struct(Vec<LowTy>),
    /// A tagged union, i.e. an Algebraic Data Type
    Union(Vec<LowTy>),
    Bool,
    Never,
}

/// An expression in LowIR
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowIR {
    Unit,
    BoolConst(bool),
    BoolOp {
        op: BoolOp,
        lhs: Box<LowIR>,
        rhs: Box<LowIR>,
    },
    IntConst(u64),
    SizedIntConst(u32, u64),
    IntOp {
        op: IntOp,
        lhs: Box<LowIR>,
        rhs: Box<LowIR>,
    },
    CompOp {
        op: CompOp,
        lhs: Box<LowIR>,
        rhs: Box<LowIR>,
    },
    Let(Sym, Box<LowIR>, Box<LowIR>),
    Local(Sym),
    Global(Sym, ScopeId, String),
    TypedGlobal(LowTy, String),
    /// The symbols are only so that other struct elements can refer to them, the members must be sorted by RawSym
    Struct(Vec<(Sym, LowIR)>),
    Project(Box<LowIR>, usize),
    /// Wraps an owned closure and turns it into a borrowed one (takes a pointer to the lctxironment and bitcasts it to `void*`)
    ClosureBorrow(Box<LowIR>),
    /// An owned closure
    Closure {
        fun_name: String,
        attrs: Vec<FunAttr>,
        arg_name: Sym,
        arg_ty: LowTy,
        upvalues: Vec<(Sym, LowTy)>,
        ret_ty: LowTy,
        body: Box<LowIR>,
    },
    /// A tagged union value
    Variant(u64, LowTy, Box<LowIR>),
    /// A switch on consecutive i64's
    Switch(Box<LowIR>, Vec<LowIR>),
    /// Switch + branch + multiple phis
    MultiSwitch {
        switch_on: Box<LowIR>,
        cases: Vec<(BlockId, LowIR)>,
        blocks: Vec<(Vec<Phi>, BlockId, LowIR)>,
    },
    Unreachable,
    Branch(BlockId),
    If {
        cond: Box<LowIR>,
        yes: Box<LowIR>,
        no: Box<LowIR>,
    },
    Call(Box<LowIR>, Box<LowIR>),
    CallM(Box<LowIR>, Vec<LowIR>),
    /// An owned closure
    ClosureM {
        fun_name: String,
        attrs: Vec<FunAttr>,
        args: Vec<(Sym, LowTy)>,
        upvalues: Vec<(Sym, LowTy)>,
        ret_ty: LowTy,
        body: Box<LowIR>,
    },
}

fn lower_cons(cons: TagId, ty: &Elab, lctx: &LCtx) -> LowIR {
    let sid = if let Elab::Data(_, sid, _) = ty.result().head() {
        *sid
    } else {
        panic!("wrong type")
    };
    let scope = ScopeId::Struct(sid, Box::new(lctx.scope()));
    let raw = lctx.bindings().tag_name(cons);
    let idx = lctx
        .database()
        .symbols(scope)
        .iter()
        .enumerate()
        .find(|(_, s)| s.raw() == raw)
        .unwrap()
        .0 as u64;
    let result_ty = ty.result().as_low_ty(lctx);

    fn accumulate(t: &Elab, v: &mut Vec<LowTy>, lctx: &LCtx) {
        match t {
            Elab::Fun(_, from, to) => {
                v.push(from.as_low_ty(lctx));
                accumulate(to, v, lctx);
            }
            _ => (),
        }
    }

    let mut arg_tys = Vec::new();
    accumulate(ty, &mut arg_tys, lctx);

    let low_args: Vec<_> = arg_tys
        .into_iter()
        .enumerate()
        .map(|(i, x)| (lctx.bindings_mut().create(format!("_carg{}", i)), x))
        .collect();
    let body = LowIR::Variant(
        idx,
        result_ty,
        Box::new(LowIR::Struct(
            low_args
                .iter()
                .map(|(s, _)| (*s, LowIR::Local(*s)))
                .collect(),
        )),
    );
    let mut i = low_args.len();
    low_args.iter().rfold(body, |body, (arg_name, arg_ty)| {
        // Thread parameters through closures as well
        i -= 1;
        let up = low_args
            .iter()
            .take(i)
            .map(|(x, y)| (*x, y.clone()))
            .collect();
        LowIR::Closure {
            fun_name: format!("$_cons_closure{}", next_closure()),
            attrs: Vec::new(),
            arg_name: *arg_name,
            arg_ty: arg_ty.clone(),
            ret_ty: body.get_type(lctx),
            body: Box::new(body),
            upvalues: up,
        }
    })
}

impl Elab {
    pub fn low_ty_of(&self, lctx: &mut LCtx) -> Option<LowTy> {
        Some(match self {
            // Guaranteed erasure for multiplicity-0 types
            // Disabled right now because of bad interaction with metavariables, and QTT stuff is going to get rewritten soon anyway
            // _ if self.get_type(lctx).multiplicity(lctx) == Mult::Zero => LowTy::Unit,
            Elab::Unit => LowTy::Unit,
            Elab::I32(_) => LowTy::Int(32),
            Elab::Var(_, x, ty) => {
                if ty.is_concrete(lctx) {
                    return lctx.low_ty(*x);
                } else {
                    return None;
                }
            }
            Elab::Pair(a, b) => {
                let a = a.low_ty_of(lctx)?;
                let b = b.low_ty_of(lctx)?;
                LowTy::Struct(vec![a, b])
            }
            // We compile records in either "module mode" or "struct mode"
            // Inline structs (ones that weren't in the original code) are always compiled in struct mode
            // Interned structs (ones that were in the original code) are compiled in module mode
            // Currently, structs compiled in "struct mode" have ordered definitions and don't allow recursion
            Elab::StructInline(iv) => {
                let mut rv = Vec::new();
                for (name, val) in iv {
                    if let Some(ty) = val.low_ty_of(lctx) {
                        lctx.set_low_ty(*name, ty.clone());
                        rv.push((*name, ty))
                    }
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowTy::Struct(rv.into_iter().map(|(_, x)| x).collect())
            }
            Elab::StructIntern(id) => {
                let scope = ScopeId::Struct(*id, Box::new(lctx.scope()));

                debug_assert!(
                    !lctx.low_tys.keys().any(|t| self.uses(*t)),
                    "Typechecker failed to inline capturing struct"
                );

                // Compile it in "module mode": all members are global functions, like top-level definitions
                let mut rv = Vec::new();
                let s = lctx.database().symbols(scope.clone());
                for name in s.iter() {
                    match lctx.database().low_ty(scope.clone(), **name) {
                        Ok(ty) => rv.push((**name, ty)),
                        Err(LowError::Polymorphic) => return None,
                        Err(LowError::NoElab) => panic!("Shouldn't have gotten here"),
                    }
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowTy::Struct(rv.into_iter().map(|(_, x)| x).collect())
            }
            Elab::Block(v) => {
                for i in v.iter().take(v.len() - 1) {
                    match i {
                        ElabStmt::Def(name, val) => {
                            let ty = val.low_ty_of(lctx)?;
                            lctx.set_low_ty(*name, ty);
                        }
                        _ => (),
                    }
                }
                match v.last().unwrap() {
                    ElabStmt::Expr(e) => e.low_ty_of(lctx)?,
                    ElabStmt::Def(_, _) => LowTy::Unit,
                }
            }
            Elab::Fun(cl, from, body) => {
                let mut lctx = lctx.clone();
                lctx.add_clos(&cl);

                if !self.get_type(&lctx).is_concrete(&lctx) {
                    // Don't lower this function yet, wait until it's called
                    return None;
                }

                let mut cln = Cloner::new(&lctx);

                // Use the closure we already created for upvalues
                let upvalues: Vec<_> = cl
                    .tys
                    .iter()
                    .filter_map(|(k, t)| {
                        if !lctx.vals.contains_key(k) && **t != Elab::Bottom && t.is_concrete(&lctx)
                        {
                            Some(t.cloned(&mut cln).whnf(&mut lctx).as_low_ty(&lctx))
                        } else {
                            None
                        }
                    })
                    .collect();

                let fresh = lctx.bindings_mut().create("_arg".to_string());
                let param = LowIR::Local(fresh);
                let _ = from.compile_match(&mut lctx, &from, param);
                let ret_ty = body.low_ty_of(&mut lctx).unwrap();

                LowTy::ClosOwn {
                    from: Box::new(from.as_low_ty(&lctx)),
                    to: Box::new(ret_ty),
                    upvalues,
                }
            }
            Elab::CaseOf(_, cases, _) => {
                let mut ty = None;
                for (pat, body) in cases {
                    // We need to type the variables from the pattern before we can type the body
                    pat.lower(LowIR::Unit, lctx);

                    let this_ty = body.low_ty_of(lctx);
                    if ty.is_none() {
                        assert!(this_ty.is_some());
                        ty = this_ty;
                    } else {
                        // Make sure all cases have the same type
                        assert_eq!(ty, this_ty);
                    }
                }
                ty.unwrap()
            }
            Elab::App(f, x) => match f.get_type_rec(lctx) {
                Elab::Fun(_, _, _) => {
                    if let Some(f) = f.low_ty_of(lctx) {
                        match f {
                            LowTy::ClosOwn { to, .. } => *to,
                            LowTy::ClosRef { to, .. } => *to,
                            _ => panic!("not function type"),
                        }
                    } else {
                        // Inline it
                        let s = self.cloned(&mut Cloner::new(&lctx)).whnf(lctx);
                        // Only recurse if it actually did something (it's not an App anymore)
                        match &s {
                            Elab::App(f, _) => {
                                // If it is still an App, it might be a partial application of a data constructor that makes it monomorphic
                                if let Elab::Cons(cons, cty) = f.head() {
                                    let ty = self.get_type(lctx);
                                    if ty.is_concrete(lctx) {
                                        // App(App(_, _), _) <-> Fun(_, Fun(_, Fun(_, Fun(_, _))))
                                        //     App(_, _)     <->        Fun(_, Fun(_, Fun(_, _)))
                                        //         _         <->               Fun(_, Fun(_, _))
                                        fn match_len<'e>(a: &Elab, b: &'e Elab) -> &'e Elab {
                                            match (a, b) {
                                                (Elab::App(f, _), Elab::Fun(_, _, to)) => {
                                                    match_len(f, to)
                                                }
                                                _ => b,
                                            }
                                        }
                                        let tail = match_len(&s, cty);

                                        let mut tctx = crate::bicheck::TCtx::new(lctx);
                                        tctx.extend_metas(tail.fvs(lctx));
                                        let mut tcons = Vec::new();
                                        if !tail.unify(&ty, &tctx, &mut tcons) {
                                            panic!(
                                                "Couldn't unify {} and {}",
                                                tail.pretty(lctx).ansi_string(),
                                                ty.pretty(lctx).ansi_string()
                                            );
                                        }
                                        for (k, v) in tcons {
                                            eprintln!(
                                                "MetaL {} := {}",
                                                k.pretty(lctx).ansi_string(),
                                                v.pretty(lctx).ansi_string()
                                            );
                                            lctx.set_val(k, v);
                                        }

                                        let cons = lower_cons(*cons, cty, lctx);
                                        fn accumulate(
                                            cons: LowIR,
                                            t: &Elab,
                                            lctx: &mut LCtx,
                                        ) -> LowIR {
                                            match t {
                                                Elab::App(f, x) => {
                                                    let f = accumulate(cons, f, lctx);
                                                    LowIR::Call(
                                                        Box::new(f.borrow(lctx)),
                                                        Box::new(x.as_low(lctx).unwrap()),
                                                    )
                                                }
                                                _ => cons,
                                            }
                                        }
                                        return Some(accumulate(cons, &s, lctx).get_type(lctx));
                                    }
                                }
                                return None;
                            }
                            _ => s.low_ty_of(lctx)?,
                        }
                    }
                }
                Elab::App(_, _) => LowTy::Struct(vec![f.low_ty_of(lctx)?, x.low_ty_of(lctx)?]),
                x => panic!("not function type: {}", x.pretty(lctx).ansi_string()),
            },
            Elab::Project(r, m) => {
                let ty = r.get_type(lctx);
                let mut list: Vec<_> = match ty {
                    Elab::StructIntern(id) => {
                        let scope = ScopeId::Struct(id, Box::new(lctx.scope()));
                        lctx.database()
                            .symbols(scope.clone())
                            .iter()
                            .map(|name| name.raw())
                            .collect()
                    }
                    Elab::StructInline(v) => v.into_iter().map(|(name, _)| name.raw()).collect(),
                    x => panic!("not a struct: {:?}", x),
                };
                list.sort();
                let idx = list.binary_search(&m).unwrap();
                let r = r.low_ty_of(lctx)?;
                match r {
                    LowTy::Struct(v) => v[idx].clone(),
                    _ => panic!("not struct type"),
                }
            }
            Elab::Builtin(bu) if bu.is_binop() => LowTy::ClosOwn {
                from: Box::new(LowTy::Int(32)),
                upvalues: Vec::new(),
                to: Box::new(LowTy::ClosOwn {
                    from: Box::new(LowTy::Int(32)),
                    to: Box::new(LowTy::Int(32)),
                    upvalues: vec![LowTy::Int(32)],
                }),
            },
            // Type erasure
            Elab::Builtin(Builtin::Int) | Elab::Type(_) | Elab::Union(_) => LowTy::Unit,
            Elab::Data(_, _, _) => LowTy::Unit,
            Elab::Cons(cons, t) => {
                if t.is_concrete(lctx) {
                    lower_cons(*cons, t, lctx).get_type(lctx)
                } else {
                    return None;
                }
            }
            _ => panic!("couldn't low-ty {}", self.pretty(lctx).ansi_string()),
        })
    }

    /// Convert to LowIR, within the Salsa framework. Returns `None` if it's polymorphic
    ///
    /// Most work should be done here and not in `LowIR::codegen()`, since we want Salsa memoization
    pub fn as_low(&self, lctx: &mut LCtx) -> Option<LowIR> {
        Some(match self {
            // Guaranteed erasure for multiplicity-0 types
            // _ if self.get_type(lctx).multiplicity(lctx) == Mult::Zero => LowIR::Unit,
            Elab::Unit => LowIR::Unit,
            Elab::I32(i) => LowIR::IntConst(unsafe { std::mem::transmute::<i32, u32>(*i) } as u64),
            Elab::Var(_, x, ty) => {
                if ty.is_concrete(lctx) {
                    return lctx
                        .database()
                        .mangle(lctx.scope(), *x)
                        .map(|s| LowIR::Global(*x, lctx.scope(), s))
                        .or_else(|| {
                            if lctx.low_tys.contains_key(x) {
                                Some(LowIR::Local(*x))
                            } else {
                                None
                            }
                        });
                } else {
                    return None;
                }
            }
            Elab::Pair(a, b) => {
                let a = a.as_low(lctx)?;
                let b = b.as_low(lctx)?;
                let fresh = lctx.bindings_mut().create("_".to_string());
                LowIR::Struct(vec![(fresh, a), (fresh, b)])
            }
            // We compile records in either "module mode" or "struct mode"
            // Inline structs (ones that weren't in the original code) are always compiled in struct mode
            // Interned structs (ones that were in the original code) are compiled in module mode
            Elab::StructInline(iv) => {
                let mut rv = Vec::new();
                for (name, val) in iv {
                    let ty = val.low_ty_of(lctx)?;
                    lctx.set_low_ty(*name, ty);
                }
                for (name, val) in iv {
                    rv.push((*name, val.as_low(lctx)?));
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowIR::Struct(rv)
            }
            Elab::StructIntern(id) => {
                let scope = ScopeId::Struct(*id, Box::new(lctx.scope()));

                debug_assert!(
                    !lctx.low_tys.keys().any(|t| self.uses(*t)),
                    "Typechecker failed to inline capturing struct"
                );

                // Compile it in "module mode": all members are global functions, like top-level definitions
                let mut rv = Vec::new();
                let s = lctx.database().symbols(scope.clone());
                for name in s.iter() {
                    match lctx.database().low_fun(scope.clone(), **name) {
                        Ok(fun) => rv.push((
                            **name,
                            LowIR::Global(**name, scope.clone(), fun.name.clone()),
                        )),
                        Err(LowError::Polymorphic) => return None,
                        Err(LowError::NoElab) => panic!("Shouldn't have gotten here"),
                    }
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowIR::Struct(rv)
            }
            Elab::Block(v) => {
                let lows: Vec<(Sym, LowIR)> = v
                    .iter()
                    .take(v.len() - 1)
                    .filter_map(|x| match x {
                        ElabStmt::Expr(_) => None,
                        ElabStmt::Def(name, val) => Some({
                            let ty = val.low_ty_of(lctx)?;
                            lctx.set_low_ty(*name, ty);
                            let val = val.as_low(lctx)?;
                            (*name, val)
                        }),
                    })
                    .collect();
                let last = match v.last().unwrap() {
                    ElabStmt::Expr(e) => e.as_low(lctx)?,
                    ElabStmt::Def(_, _) => LowIR::Unit,
                };
                lows.into_iter().rfold(last, |acc, (name, val)| {
                    LowIR::Let(name, Box::new(val), Box::new(acc))
                })
            }
            Elab::Fun(cl, from, body) => {
                lctx.add_clos(&cl);

                if !self.get_type(lctx).is_concrete(lctx) {
                    // Don't lower this function yet, wait until it's called
                    return None;
                }

                let mut cln = Cloner::new(lctx);

                // Use the closure we already created for upvalues
                let upvalues: Vec<_> = cl
                    .tys
                    .iter()
                    .filter_map(|(k, t)| {
                        if !lctx.vals.contains_key(k) && **t != Elab::Bottom && t.is_concrete(lctx)
                        {
                            Some((*k, t.cloned(&mut cln).whnf(lctx).as_low_ty(lctx)))
                        } else {
                            None
                        }
                    })
                    .collect();

                let fresh = lctx.bindings_mut().create("_arg".to_string());
                let param = LowIR::Local(fresh);
                let nothing = from.compile_match(lctx, &from, param);

                let body = body.as_low(lctx).unwrap();
                // We ignore `nothing`, but we need to chain them
                let body = LowIR::Let(
                    lctx.bindings_mut().create("_".to_string()),
                    Box::new(nothing),
                    Box::new(body),
                );

                let ret_ty = body.get_type(&lctx);
                LowIR::Closure {
                    fun_name: format!("$_closure{}", next_closure()),
                    attrs: Vec::new(),
                    arg_name: fresh,
                    arg_ty: from.as_low_ty(lctx),
                    ret_ty,
                    body: Box::new(body),
                    upvalues,
                }
            }
            Elab::CaseOf(val, cases, _) => {
                let val = val.as_low(lctx)?;
                let ty = val.get_type(lctx);
                let fresh = lctx.bindings_mut().create("$_scrutinee".to_string());
                lctx.set_low_ty(fresh, ty);
                let param = LowIR::Local(fresh);

                let body = cases.iter().rfold(LowIR::Unreachable, |rest, (pat, body)| {
                    let did_match = pat.lower(param.clone(), lctx);
                    let body = body.as_low(lctx).unwrap();
                    LowIR::If {
                        cond: Box::new(did_match),
                        yes: Box::new(body),
                        no: Box::new(rest),
                    }
                });
                LowIR::Let(fresh, Box::new(val), Box::new(body))
            }
            Elab::App(f, x) => match f.get_type_rec(lctx) {
                Elab::Fun(cl, from, _) => {
                    lctx.add_clos(&cl);
                    // In case it has variables that already have values etc.
                    let from = from.normal(lctx);

                    // We borrow both the function and the argument
                    if let Some(f) = f.as_low(lctx) {
                        let f = f.borrow(lctx);
                        let x = x
                            .as_low(lctx)?
                            .cast(&x.get_type(lctx), &from, lctx)
                            .borrow(lctx);
                        LowIR::Call(Box::new(f), Box::new(x))
                    } else {
                        match &**f {
                            Elab::Var(_, name, _) => {
                                if let Some((mono, ty)) = lctx.mono(*name, x) {
                                    return Some(LowIR::TypedGlobal(ty, mono));
                                } else {
                                    let s = self.cloned(&mut Cloner::new(lctx)).whnf(lctx);
                                    // Only recurse if it actually did something (it's not an App anymore)
                                    match s {
                                        Elab::App(_, _) => return None,
                                        s => {
                                            let mut low = s.as_low(lctx)?;
                                            let ty = s.low_ty_of(lctx)?;
                                            match &mut low {
                                                LowIR::Closure {
                                                    fun_name, upvalues, ..
                                                } if upvalues.is_empty() => {
                                                    *fun_name = Doc::start("$mono$")
                                                        .chain(name.pretty(lctx))
                                                        .add("$")
                                                        .chain(x.pretty(lctx))
                                                        .raw_string();
                                                    lctx.set_mono(
                                                        *name,
                                                        x.cloned(&mut Cloner::new(&lctx)),
                                                        fun_name.to_string(),
                                                        ty,
                                                    );
                                                }
                                                _ => (),
                                            };
                                            low
                                        }
                                    }
                                }
                            }
                            _ => {
                                // Inline it
                                let s = self.cloned(&mut Cloner::new(lctx)).whnf(lctx);
                                // Only recurse if it actually did something (it's not an App anymore)
                                match &s {
                                    Elab::App(f, _) => {
                                        // If it is still an App, it might be a partial application of a data constructor that makes it monomorphic
                                        if let Elab::Cons(cons, cty) = f.head() {
                                            let ty = self.get_type(lctx);
                                            if ty.is_concrete(lctx) {
                                                // App(App(_, _), _) <-> Fun(_, Fun(_, Fun(_, Fun(_, _))))
                                                //     App(_, _)     <->        Fun(_, Fun(_, Fun(_, _)))
                                                //         _         <->               Fun(_, Fun(_, _))
                                                fn match_len<'e>(
                                                    a: &Elab,
                                                    b: &'e Elab,
                                                ) -> &'e Elab
                                                {
                                                    match (a, b) {
                                                        (Elab::App(f, _), Elab::Fun(_, _, to)) => {
                                                            match_len(f, to)
                                                        }
                                                        _ => b,
                                                    }
                                                }
                                                let tail = match_len(&s, cty);

                                                let mut tctx = crate::bicheck::TCtx::new(lctx);
                                                tctx.extend_metas(tail.fvs(lctx));
                                                let mut tcons = Vec::new();
                                                if !tail.unify(&ty, &tctx, &mut tcons) {
                                                    panic!(
                                                        "Couldn't unify {} and {}",
                                                        tail.pretty(lctx).ansi_string(),
                                                        ty.pretty(lctx).ansi_string()
                                                    );
                                                }
                                                for (k, v) in tcons {
                                                    eprintln!(
                                                        "MetaL {} := {}",
                                                        k.pretty(lctx).ansi_string(),
                                                        v.pretty(lctx).ansi_string()
                                                    );
                                                    lctx.set_val(k, v);
                                                }

                                                let cons = lower_cons(*cons, cty, lctx);
                                                fn accumulate(
                                                    cons: LowIR,
                                                    t: &Elab,
                                                    lctx: &mut LCtx,
                                                ) -> LowIR
                                                {
                                                    match t {
                                                        Elab::App(f, x) => {
                                                            let f = accumulate(cons, f, lctx);
                                                            LowIR::Call(
                                                                Box::new(f.borrow(lctx)),
                                                                Box::new(x.as_low(lctx).unwrap()),
                                                            )
                                                        }
                                                        _ => cons,
                                                    }
                                                }
                                                return Some(accumulate(cons, &s, lctx));
                                            }
                                        }
                                        return None;
                                    }
                                    _ => s.as_low(lctx)?,
                                }
                            }
                        }
                    }
                }
                Elab::App(_, _) => {
                    let fresh = lctx.bindings_mut().create("_".to_string());
                    LowIR::Struct(vec![(fresh, f.as_low(lctx)?), (fresh, f.as_low(lctx)?)])
                }
                x => panic!("not function type: {}", x.pretty(lctx).ansi_string()),
            },
            Elab::Project(r, m) => {
                let ty = r.get_type(lctx);
                let mut list: Vec<_> = match ty {
                    Elab::StructIntern(id) => {
                        let scope = ScopeId::Struct(id, Box::new(lctx.scope()));
                        lctx.database()
                            .symbols(scope.clone())
                            .iter()
                            .map(|name| name.raw())
                            .collect()
                    }
                    Elab::StructInline(v) => v.into_iter().map(|(name, _)| name.raw()).collect(),
                    x => panic!("not a struct: {:?}", x),
                };
                list.sort();
                let idx = list.binary_search(&m).unwrap();
                let r = r.as_low(lctx)?;
                LowIR::Project(Box::new(r), idx)
            }
            // We essentially create a lambda for operators, because they need to be able to curry too
            // Eventually these will be in the builtin part of the standard library and we'll just call them
            Elab::Builtin(bu) if bu.is_binop() => {
                let a = lctx.bindings_mut().create("_a".to_string());
                let b = lctx.bindings_mut().create("_b".to_string());
                LowIR::Closure {
                    arg_name: a,
                    fun_name: format!("binop${}${}", bu, next_closure()),
                    attrs: vec![FunAttr::AlwaysInline],
                    arg_ty: LowTy::Int(32),
                    upvalues: Vec::new(),
                    ret_ty: LowTy::ClosOwn {
                        from: Box::new(LowTy::Int(32)),
                        to: Box::new(LowTy::Int(32)),
                        upvalues: vec![LowTy::Int(32)],
                    },
                    body: Box::new(LowIR::Closure {
                        arg_name: b,
                        fun_name: format!("binop2${}${}", bu, next_closure()),
                        attrs: vec![FunAttr::AlwaysInline],
                        arg_ty: LowTy::Int(32),
                        upvalues: vec![(a, LowTy::Int(32))],
                        ret_ty: LowTy::Int(32),
                        body: Box::new(LowIR::IntOp {
                            op: todo!("get rid of this module"),
                            lhs: Box::new(LowIR::Local(a)),
                            rhs: Box::new(LowIR::Local(b)),
                        }),
                    }),
                }
            }
            // Type erasure
            Elab::Builtin(Builtin::Int) | Elab::Type(_) | Elab::Union(_) => LowIR::Unit,
            Elab::Data(_, _, _) => LowIR::Unit,
            Elab::Cons(id, t) => {
                // We need to monomorphize polymorphic data constructors, too
                if !t.is_concrete(lctx) {
                    return None;
                }
                lower_cons(*id, t, lctx)
            }
            _ => panic!("{:?} not supported (ir)", self),
        })
    }

    /// Is this a concrete type, i.e., we don't need to monomorphize it?
    pub fn is_concrete(&self, lctx: &LCtx) -> bool {
        match self {
            Elab::Var(_, s, _) if lctx.database().elab(lctx.scope(), *s).is_some() => lctx
                .database()
                .elab(lctx.scope(), *s)
                .unwrap()
                .is_concrete(lctx),
            Elab::Var(_, s, _) if lctx.vals.contains_key(s) => {
                lctx.val(*s).unwrap().is_concrete(lctx)
            }
            Elab::Var(_, _, _) => false,
            Elab::Pair(x, y) => x.is_concrete(lctx) && y.is_concrete(lctx),
            Elab::StructInline(v) => v.iter().all(|(_, x)| x.is_concrete(lctx)),
            Elab::Type(_)
            | Elab::Unit
            | Elab::Builtin(_)
            | Elab::I32(_)
            | Elab::StructIntern(_)
            | Elab::Bottom
            | Elab::Data(_, _, _)
            | Elab::Cons(_, _) => true,
            Elab::Binder(_, t) => t.is_concrete(lctx),
            Elab::Fun(cl, from, to) => {
                let mut lctx = lctx.clone();
                lctx.add_clos(cl);
                from.is_concrete(&lctx) && to.is_concrete(&lctx)
            }
            Elab::Union(v) => v.iter().all(|x| x.is_concrete(lctx)),
            Elab::App(f, x) => f.is_concrete(lctx) && x.is_concrete(lctx),
            // This shouldn't happen unless the first param is neutral and thus not concrete
            Elab::Project(_, _) | Elab::Block(_) | Elab::Top | Elab::CaseOf(_, _, _) => false,
        }
    }

    /// Convert a `Elab` representing a type to the `LowTy` that Elabs of that type are stored as
    pub fn as_low_ty(&self, lctx: &LCtx) -> LowTy {
        match self {
            Elab::Var(_, v, _) => {
                if let Some(t) = lctx
                    .database()
                    .elab(lctx.scope(), *v)
                    .or_else(|| lctx.val(*v))
                {
                    t.as_low_ty(lctx)
                } else {
                    panic!(
                        "Unbound variable {} has no LowTy",
                        v.pretty(lctx).ansi_string()
                    )
                }
            }
            Elab::Builtin(Builtin::Int) | Elab::I32(_) => LowTy::Int(32),
            Elab::Unit => LowTy::Unit,
            Elab::Binder(_, t) => t.as_low_ty(lctx),
            Elab::Fun(cl, from, to) => {
                eprintln!("Low-Ty-ing {}", self.pretty(lctx).ansi_string());

                let mut lctx = lctx.clone();
                lctx.add_clos(&cl);

                // TODO do we need whnf here?
                let from = from
                    // .cloned(&mut Cloner::new(&lctx))
                    // .whnf(&mut lctx)
                    .as_low_ty(&lctx);
                let to = to
                    // .cloned(&mut Cloner::new(&lctx))
                    // .whnf(&mut lctx)
                    .as_low_ty(&lctx);
                LowTy::ClosRef {
                    from: Box::new(from),
                    to: Box::new(to),
                }
            }
            Elab::Pair(a, b) => LowTy::Struct(vec![a.as_low_ty(lctx), b.as_low_ty(lctx)]),
            Elab::StructInline(v) => {
                let mut v: Vec<_> = v.iter().collect();
                v.sort_by_key(|(x, _)| x.raw());
                LowTy::Struct(v.into_iter().map(|(_, v)| v.as_low_ty(lctx)).collect())
            }
            // Attach data to tags
            Elab::App(f, x) => match &**f {
                // Ignore the tag
                Elab::Cons(_, _) => x.as_low_ty(lctx),
                _ => match f.head() {
                    Elab::Cons(_, _) => LowTy::Struct(vec![f.as_low_ty(lctx), x.as_low_ty(lctx)]),
                    Elab::Data(_, s, _) => {
                        let scope = ScopeId::Struct(*s, Box::new(lctx.scope()));
                        LowTy::Union(
                            lctx.database()
                                .symbols(scope.clone())
                                .iter()
                                .map(|x| lctx.database().elab(scope.clone(), **x).unwrap())
                                .filter_map(|x| {
                                    let mut lctx = lctx.clone();
                                    let t = x.get_type(&lctx).whnf(&mut lctx);
                                    // We unify here, so for
                                    // ```
                                    // type T: fun Type => Type of
                                    //   A : fun Int => T Int
                                    //   B : fun (a:Type) a => T a
                                    // ```
                                    // if you have a `T Bool`, we represent that as just `{{}, Bool}` since we know it's B and that a is Bool
                                    let result = t.result();
                                    let mut tctx = crate::bicheck::TCtx::new(&lctx);
                                    tctx.extend_metas(result.fvs(&tctx));
                                    let mut tcons = Vec::new();
                                    if !result.unify(self, &tctx, &mut tcons) {
                                        // TODO: this narrowing of GADTs based on type works here, but not in pattern matching yet. So when it does, turn it on here.
                                        // return None;
                                    }
                                    for (k, v) in tcons {
                                        lctx.set_val(k, v);
                                    }

                                    fn accumulate(t: &Elab, v: &mut Vec<LowTy>, lctx: &LCtx) {
                                        match t {
                                            Elab::Fun(_, from, to) => {
                                                v.push(from.as_low_ty(lctx));
                                                accumulate(to, v, lctx);
                                            }
                                            _ => (),
                                        }
                                    }
                                    let mut v = Vec::new();
                                    accumulate(&t, &mut v, &lctx);
                                    Some(if v.is_empty() {
                                        LowTy::Unit
                                    } else {
                                        LowTy::Struct(v)
                                    })
                                })
                                .collect(),
                        )
                    }
                    _ => panic!("{:?} is not supported", f),
                },
            },
            Elab::Union(v) => LowTy::Union(v.iter().map(|x| x.as_low_ty(lctx)).collect()),
            // Type erasure
            Elab::Type(_) => LowTy::Unit,
            Elab::Data(_, s, _) => {
                let scope = ScopeId::Struct(*s, Box::new(lctx.scope()));
                LowTy::Union(
                    lctx.database()
                        .symbols(scope.clone())
                        .iter()
                        .map(|x| lctx.database().elab(scope.clone(), **x).unwrap())
                        .filter_map(|x| {
                            let t = x.get_type(lctx);

                            fn accumulate(t: &Elab, v: &mut Vec<LowTy>, lctx: &LCtx) {
                                match t {
                                    Elab::Fun(_, from, to) => {
                                        v.push(from.as_low_ty(lctx));
                                        accumulate(to, v, lctx);
                                    }
                                    _ => (),
                                }
                            }
                            let mut v = Vec::new();
                            accumulate(&t, &mut v, lctx);
                            Some(if v.is_empty() {
                                LowTy::Unit
                            } else {
                                LowTy::Struct(v)
                            })
                        })
                        .collect(),
                )
            }
            _ => panic!("{} is not supported", self.pretty(lctx).ansi_string()),
        }
    }

    /// Compile this pattern to code that binds all binders and returns ()
    ///
    /// This function clones `param`, so it should be a `LowIR::Local`
    fn compile_match(
        &self,
        lctx: &mut LCtx,
        // The parameter type, which might need to be casted etc.
        ty: &Elab,
        param: LowIR,
    ) -> LowIR {
        let ty = match ty {
            Elab::Binder(_, t) => t,
            t => t,
        };
        match (self, ty) {
            // TODO var case that checks both `lctx` and `need_phi`
            (Elab::Binder(x, t), _) => {
                let lty = t.as_low_ty(&lctx);
                lctx.set_low_ty(*x, lty.clone());
                LowIR::Let(
                    *x,
                    Box::new(param.clone()),
                    Box::new(t.compile_match(lctx, ty, param)),
                )
            }
            (Elab::StructIntern(i), _) => ScopeId::Struct(*i, Box::new(lctx.scope()))
                .inline(lctx)
                .compile_match(lctx, ty, param),
            (Elab::StructInline(v), Elab::StructInline(tv)) => {
                let mut v: Vec<_> = v.iter().map(|(name, val)| (*name, val)).collect();
                v.sort_by_key(|(s, _)| s.raw());
                let mut tv: Vec<_> = tv.iter().map(|(name, val)| (*name, val)).collect();
                tv.sort_by_key(|(s, _)| s.raw());

                let mut body = LowIR::BoolConst(true);
                for (i, ((_name, val), (_, ty))) in v.into_iter().zip(tv).enumerate() {
                    let param = LowIR::Project(Box::new(param.clone()), i);
                    let rest = val.compile_match(lctx, ty, param);
                    body = LowIR::Let(
                        lctx.bindings_mut().create("_".into()),
                        Box::new(body),
                        Box::new(rest),
                    );
                }
                body
            }
            (Elab::Pair(x, y), Elab::Pair(tx, ty)) => {
                let x_param = LowIR::Project(Box::new(param.clone()), 0);
                let y_param = LowIR::Project(Box::new(param), 1);
                let x = x.compile_match(lctx, tx, x_param);
                let y = y.compile_match(lctx, ty, y_param);
                LowIR::Let(
                    lctx.bindings_mut().create("_".into()),
                    Box::new(x),
                    Box::new(y),
                )
            }
            // Don't bind anything
            _ => LowIR::BoolConst(true),
        }
    }
}

/// Get the width of the smallest IntType that can differentiate between all the things in `v`.
/// One of `i1, i8, i16, i32, i64`, or 0 if no tag is needed.
pub fn tag_width<T>(v: &[T]) -> u32 {
    let l = v.len();
    if l <= 1 {
        0
    } else if l <= 2 {
        1
    } else if l <= 256 {
        8
    } else if l <= 1 << 16 {
        16
    } else if l <= 1 << 32 {
        32
    } else {
        64
    }
}

// impl Builtin {
//     pub fn int_op(self) -> Option<IntOp> {
//         match self {
//             Builtin::Add => Some(IntOp::Add),
//             Builtin::Sub => Some(IntOp::Sub),
//             Builtin::Mul => Some(IntOp::Mul),
//             Builtin::Div => Some(IntOp::Div),
//             _ => None,
//         }
//     }
// }

impl LowIR {
    fn cast(self, from: &Elab, to: &Elab, lctx: &mut LCtx) -> Self {
        match (from, to) {
            (cur, ty) if cur == ty => self,
            (_, Elab::Binder(_, t)) => self.cast(from, t, lctx),
            (Elab::Union(from), Elab::Union(vto)) => {
                let mut tctx = TCtx::new(lctx);
                let fresh = lctx.bindings_mut().create("union".to_string());
                let tag = LowIR::Project(Box::new(LowIR::Local(fresh)), 0);
                let mut cases: Vec<LowIR> = Vec::new();
                for ty in from.iter() {
                    if let Some((idx, _)) = vto
                        .iter()
                        .enumerate()
                        .find(|(_, x)| x.unify(ty, &mut tctx, &mut Vec::new()))
                    {
                        cases.push(LowIR::Variant(
                            idx as u64,
                            to.as_low_ty(lctx),
                            Box::new(LowIR::Local(fresh)),
                        ));
                    } else {
                        panic!("none matched");
                    }
                }
                LowIR::Let(
                    fresh,
                    Box::new(self),
                    Box::new(LowIR::Switch(Box::new(tag), cases)),
                )
            }
            (_, Elab::Union(vto)) => {
                let mut tctx = TCtx::new(lctx);
                for (i, t) in vto.iter().enumerate() {
                    if from.unify(t, &mut tctx, &mut Vec::new()) {
                        let r = self.cast(from, t, lctx);
                        return LowIR::Variant(i as u64, to.as_low_ty(lctx), Box::new(r));
                    }
                }
                panic!(
                    "none matched {} --> {}",
                    from.pretty(lctx).ansi_string(),
                    to.pretty(lctx).ansi_string()
                );
            }
            _ => self,
        }
    }

    pub fn borrow(self, lctx: &LCtx) -> Self {
        if let LowTy::ClosOwn { .. } = self.get_type(lctx) {
            LowIR::ClosureBorrow(Box::new(self))
        } else {
            self
        }
    }

    pub fn get_type(&self, lctx: &LCtx) -> LowTy {
        match self {
            LowIR::Unit => LowTy::Unit,
            LowIR::IntConst(_) => LowTy::Int(32),
            LowIR::SizedIntConst(i, _) => LowTy::Int(*i),
            LowIR::IntOp { lhs, .. } => lhs.get_type(lctx),
            LowIR::CompOp { .. } => LowTy::Bool,
            LowIR::Struct(v) => LowTy::Struct(v.iter().map(|(_, x)| x.get_type(lctx)).collect()),
            LowIR::Project(v, i) => {
                if let LowTy::Struct(v) = v.get_type(lctx) {
                    v[*i].clone()
                } else {
                    panic!("Not a struct type on project")
                }
            }
            LowIR::Let(_, _, body) => body.get_type(lctx),
            LowIR::Local(s) => lctx.low_ty(*s).unwrap(),
            LowIR::TypedGlobal(t, _) => t.clone(),
            LowIR::Global(s, scope, _) => lctx.database().low_ty(scope.clone(), *s).unwrap(),
            LowIR::Call(f, _) | LowIR::CallM(f, _) => match f.get_type(lctx) {
                LowTy::ClosRef { to, .. } | LowTy::ClosOwn { to, .. } => *to,
                _ => panic!("not a function LowTy"),
            },
            LowIR::ClosureBorrow(c) => {
                if let LowTy::ClosOwn { to, from, .. } = c.get_type(lctx) {
                    LowTy::ClosRef { to, from }
                } else {
                    panic!("ClosureBorrow inner not an owned closure")
                }
            }
            LowIR::Closure {
                arg_ty,
                ret_ty,
                upvalues,
                ..
            } => LowTy::ClosOwn {
                from: Box::new(arg_ty.clone()),
                to: Box::new(ret_ty.clone()),
                upvalues: upvalues.iter().map(|(_, t)| t.clone()).collect(),
            },
            LowIR::ClosureM {
                args,
                ret_ty,
                upvalues,
                ..
            } => todo!("LowTy::ClosOwnM"),
            //     LowTy::ClosOwn {
            //     from: Box::new(arg_ty.clone()),
            //     to: Box::new(ret_ty.clone()),
            //     upvalues: upvalues.iter().map(|(_, t)| t.clone()).collect(),
            // },
            LowIR::Variant(_, t, _) => t.clone(),
            LowIR::Switch(_, v) => v.first().unwrap().get_type(lctx),
            LowIR::BoolConst(_) => LowTy::Bool,
            LowIR::BoolOp { .. } => LowTy::Bool,
            LowIR::MultiSwitch { blocks, .. } => blocks.first().unwrap().2.get_type(lctx),
            LowIR::Unreachable => LowTy::Never,
            LowIR::Branch(_) => LowTy::Never,
            LowIR::If { yes, .. } => yes.get_type(lctx),
        }
    }
}

impl Pretty for IntOp {
    fn pretty(&self, _ctx: &impl HasBindings) -> Doc {
        match self {
            IntOp::Add => Doc::start("+"),
            IntOp::Sub => Doc::start("-"),
            IntOp::Mul => Doc::start("*"),
            IntOp::Div => Doc::start("/"),
        }
    }
}
impl Pretty for BoolOp {
    fn pretty(&self, _ctx: &impl HasBindings) -> Doc {
        match self {
            BoolOp::And => Doc::start("&&"),
            BoolOp::Or => Doc::start("||"),
        }
    }
}
impl Pretty for CompOp {
    fn pretty(&self, _ctx: &impl HasBindings) -> Doc {
        match self {
            CompOp::Eq => Doc::start("=="),
        }
    }
}

impl Pretty for Phi {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        self.result
            .pretty(ctx)
            .space()
            .add(":=")
            .space()
            .chain(Doc::start("phi").style(Style::Keyword))
            .chain(Doc::intersperse(
                self.incoming.iter().map(|(id, s)| {
                    Doc::none()
                        .space()
                        .add("[")
                        .space()
                        .add(id.0)
                        .space()
                        .add("=>")
                        .space()
                        .chain(s.pretty(ctx))
                        .space()
                        .add("]")
                }),
                Doc::none(),
            ))
    }
}

impl Pretty for LowTy {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        match self {
            LowTy::Int(s) => Doc::start("u").add(s).style(Style::Keyword),
            LowTy::VoidPtr => Doc::start("void*").style(Style::Keyword),
            LowTy::Unit => Doc::start("()").style(Style::Keyword),
            LowTy::ClosRef { from, to } => Doc::start("fun")
                .style(Style::Keyword)
                .add("(")
                .chain(from.pretty(ctx))
                .add(")")
                .space()
                .add("->")
                .space()
                .chain(to.pretty(ctx)),
            LowTy::ClosOwn { from, to, upvalues } => Doc::start("fun")
                .style(Style::Keyword)
                .add("{")
                .chain(Doc::intersperse(
                    upvalues.iter().map(|x| x.pretty(ctx)),
                    Doc::start(","),
                ))
                .add("}")
                .add("(")
                .chain(from.pretty(ctx))
                .add(")")
                .space()
                .add("->")
                .space()
                .chain(to.pretty(ctx)),
            LowTy::Struct(v) => Doc::start("{")
                .chain(Doc::intersperse(
                    v.iter().map(|x| x.pretty(ctx)),
                    Doc::start(",").space(),
                ))
                .add("}"),
            LowTy::Union(v) => Doc::start("(")
                .chain(Doc::intersperse(
                    v.iter().map(|x| x.pretty(ctx)),
                    Doc::none().space().add("|").space(),
                ))
                .add(")"),
            LowTy::Bool => Doc::start("bool").style(Style::Keyword),
            LowTy::Never => Doc::start("!").style(Style::Keyword),
        }
    }
}

impl Pretty for LowIR {
    fn pretty(&self, ctx: &impl HasBindings) -> Doc {
        match self {
            LowIR::Unit => Doc::start("()").style(Style::Literal),
            LowIR::BoolConst(b) => Doc::start(b).style(Style::Literal),
            LowIR::BoolOp { op, lhs, rhs } => lhs
                .pretty(ctx)
                .nest(Prec::Atom)
                .space()
                .chain(op.pretty(ctx))
                .space()
                .chain(rhs.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            LowIR::IntConst(i) => Doc::start(i).style(Style::Literal),
            LowIR::SizedIntConst(s, i) => Doc::start(i).add("u").add(s).style(Style::Literal),
            LowIR::IntOp { op, lhs, rhs } => lhs
                .pretty(ctx)
                .nest(Prec::Atom)
                .space()
                .chain(op.pretty(ctx))
                .space()
                .chain(rhs.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            LowIR::CompOp { op, lhs, rhs } => lhs
                .pretty(ctx)
                .nest(Prec::Atom)
                .space()
                .chain(op.pretty(ctx))
                .space()
                .chain(rhs.pretty(ctx).nest(Prec::Atom))
                .prec(Prec::App),
            LowIR::Let(k, v, body) => k
                .pretty(ctx)
                .style(Style::Binder)
                .space()
                .add(":=")
                .space()
                .chain(v.pretty(ctx).nest(Prec::App))
                .hardline()
                .chain(body.pretty(ctx))
                .prec(Prec::Term),
            LowIR::Local(s) => s.pretty(ctx),
            LowIR::Global(s, _, _) => s.pretty(ctx).style(Style::Binder),
            LowIR::TypedGlobal(_, s) => Doc::start(s).style(Style::Binder),
            LowIR::Struct(v) => Doc::start("{")
                .chain(Doc::intersperse(
                    v.iter().map(|(s, x)| {
                        Doc::none()
                            .line()
                            .chain(s.pretty(ctx))
                            .space()
                            .add(":=")
                            .space()
                            .chain(x.pretty(ctx))
                    }),
                    Doc::start(","),
                ))
                .indent()
                .line()
                .add("}")
                .prec(Prec::App),
            LowIR::Project(r, m) => r.pretty(ctx).nest(Prec::App).add(".").add(m),
            LowIR::ClosureBorrow(c) => Doc::start("ref")
                .style(Style::Keyword)
                .space()
                .chain(c.pretty(ctx))
                .prec(Prec::Term),
            LowIR::Closure {
                fun_name,
                attrs,
                arg_name,
                arg_ty,
                upvalues,
                ret_ty,
                body,
            } => Doc::start("fun")
                .style(Style::Keyword)
                .space()
                .add(fun_name)
                .debug(attrs)
                .add("(")
                .chain(arg_name.pretty(ctx).add(":").style(Style::Binder))
                .space()
                .chain(arg_ty.pretty(ctx))
                .add(")")
                .space()
                .chain(if upvalues.is_empty() {
                    Doc::none()
                } else {
                    Doc::start("with")
                        .style(Style::Keyword)
                        .space()
                        .add("{")
                        .chain(Doc::intersperse(
                            upvalues.iter().map(|(k, t)| {
                                Doc::none()
                                    .line()
                                    .chain(k.pretty(ctx))
                                    .space()
                                    .add(":")
                                    .style(Style::Binder)
                                    .space()
                                    .chain(t.pretty(ctx))
                            }),
                            Doc::start(","),
                        ))
                        .indent()
                        .line()
                        .add("}")
                        .space()
                })
                .add("->")
                .space()
                .chain(ret_ty.pretty(ctx))
                .space()
                .chain(
                    Doc::start("{")
                        .line()
                        .chain(body.pretty(ctx))
                        .indent()
                        .line()
                        .add("}"),
                )
                .prec(Prec::Term),
                LowIR::ClosureM {
                    fun_name,
                    attrs,
                    args,
                    upvalues,
                    ret_ty,
                    body,
                } => Doc::start("fun")
                    .style(Style::Keyword)
                    .space()
                    .add(fun_name)
                    .debug(attrs)
                    .add("(")
                    .chain(Doc::intersperse(args.iter().map(|(arg_name, arg_ty)|
                    arg_name.pretty(ctx).add(":").style(Style::Binder)
                    .space()
                    .chain(arg_ty.pretty(ctx))
                ), Doc::start(",").space()))
                    .add(")")
                    .space()
                    .chain(if upvalues.is_empty() {
                        Doc::none()
                    } else {
                        Doc::start("with")
                            .style(Style::Keyword)
                            .space()
                            .add("{")
                            .chain(Doc::intersperse(
                                upvalues.iter().map(|(k, t)| {
                                    Doc::none()
                                        .line()
                                        .chain(k.pretty(ctx))
                                        .space()
                                        .add(":")
                                        .style(Style::Binder)
                                        .space()
                                        .chain(t.pretty(ctx))
                                }),
                                Doc::start(","),
                            ))
                            .indent()
                            .line()
                            .add("}")
                            .space()
                    })
                    .add("->")
                    .space()
                    .chain(ret_ty.pretty(ctx))
                    .space()
                    .chain(
                        Doc::start("{")
                            .line()
                            .chain(body.pretty(ctx))
                            .indent()
                            .line()
                            .add("}"),
                    )
                    .prec(Prec::Term),
            LowIR::Variant(id, t, v) => Doc::start("{")
                .chain(t.pretty(ctx))
                .add("}")
                .add("::")
                .add(id)
                .add("(")
                .chain(v.pretty(ctx))
                .add(")"),
            LowIR::Switch(val, cases) => Doc::start("switch")
                .style(Style::Keyword)
                .space()
                .chain(val.pretty(ctx))
                .space()
                .add("{")
                .chain(Doc::intersperse(
                    cases
                        .iter()
                        .map(|x| Doc::none().line().chain(x.pretty(ctx).indent())),
                    Doc::none(),
                ))
                .indent()
                .line()
                .add("}")
                .prec(Prec::App),
            LowIR::MultiSwitch {
                switch_on,
                cases,
                blocks,
            } => {
                let switch = Doc::start("multiswitch")
                    .style(Style::Keyword)
                    .space()
                    .chain(switch_on.pretty(ctx))
                    .space()
                    .add("{")
                    .chain(Doc::intersperse(
                        cases.iter().map(|(id, x)| {
                            Doc::none().line().chain(
                                Doc::start(id.0)
                                    .add(":")
                                    .style(Style::Binder)
                                    .line()
                                    .chain(x.pretty(ctx))
                                    .indent(),
                            )
                        }),
                        Doc::none(),
                    ))
                    .line()
                    .add("}")
                    .prec(Prec::App);
                let blocks = Doc::start("where")
                    .style(Style::Keyword)
                    .space()
                    .add("{")
                    .line()
                    .chain(Doc::intersperse(
                        blocks.iter().map(|(phis, id, body)| {
                            Doc::start(id.0)
                                .add(":")
                                .style(Style::Binder)
                                .hardline()
                                .chain(Doc::intersperse(
                                    phis.iter().map(|x| x.pretty(ctx).hardline()),
                                    Doc::none(),
                                ))
                                .chain(body.pretty(ctx))
                                .indent()
                        }),
                        Doc::none().line(),
                    ))
                    .line()
                    .add("}");
                switch.space().chain(blocks)
            }
            LowIR::Unreachable => Doc::start("unreachable").style(Style::Keyword),
            LowIR::Branch(id) => Doc::start("branch")
                .style(Style::Keyword)
                .space()
                .add(id.0)
                .prec(Prec::App),
            LowIR::If { cond, yes, no } => Doc::start("if")
                .style(Style::Keyword)
                .space()
                .chain(cond.pretty(ctx))
                .space()
                .add("{")
                .line()
                .chain(yes.pretty(ctx))
                .indent()
                .line()
                .add("}")
                .space()
                .chain(
                    Doc::start("else")
                        .style(Style::Keyword)
                        .space()
                        .add("{")
                        .line()
                        .chain(no.pretty(ctx))
                        .indent()
                        .line()
                        .add("}"),
                ),
            LowIR::Call(f, x) => f
                .pretty(ctx)
                .nest(Prec::Atom)
                .add("(")
                .chain(x.pretty(ctx))
                .add(")")
                .prec(Prec::App),
            LowIR::CallM(f, v) => f
                .pretty(ctx)
                .nest(Prec::Atom)
                .add("(")
                .chain(Doc::intersperse(v.iter().map(|x|x.pretty(ctx)), Doc::start(",").space()))
                .add(")")
                .prec(Prec::App),
        }
    }
}
