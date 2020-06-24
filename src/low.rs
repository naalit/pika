//! This module describes LowIR, which should be pretty close to LLVM IR, but it doesn't involve any FFI
//! The process of lowering to LowIR uses Salsa
//! In `codegen`, we use Inkwell to convert LowIR into LLVM outside of the Salsa framework

use crate::{common::*, elab::*, term::Builtin};
use lazy_static::lazy_static;
use std::ops::{Deref, DerefMut};
use std::sync::RwLock;

pub struct LCtx<'a, T: MainGroup> {
    pub low_tys: HashMap<Sym, LowTy>,
    pub ectx: ECtx<'a, T>,
}
impl<'a, T: MainGroup> Clone for LCtx<'a, T> {
    fn clone(&self) -> Self {
        LCtx {
            low_tys: self.low_tys.clone(),
            ectx: self.ectx.clone(),
        }
    }
}
impl<'a, T: MainGroup> From<ECtx<'a, T>> for LCtx<'a, T> {
    fn from(ectx: ECtx<'a, T>) -> Self {
        LCtx {
            low_tys: HashMap::new(),
            ectx,
        }
    }
}
impl<'a, T: MainGroup> LCtx<'a, T> {
    pub fn new(db: &'a (impl Scoped + HasDatabase<DB = T>)) -> Self {
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
        let mut cloned = self.clone();
        self.database()
            .monos()
            .get(&f)?
            .iter()
            .find(|v| {
                let (k, _, _) = &***v;
                x.subtype_of(k, &mut cloned)
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
}
impl<'a, T: MainGroup> Scoped for LCtx<'a, T> {
    fn scope(&self) -> ScopeId {
        self.ectx.scope()
    }
}
impl<'a, T: MainGroup> HasBindings for LCtx<'a, T> {
    fn bindings_ref(&self) -> &Arc<RwLock<Bindings>> {
        self.database().bindings_ref()
    }
}
impl<'a, T: MainGroup> HasDatabase for LCtx<'a, T> {
    type DB = T;
    fn database(&self) -> &dyn MainGroupP<DB = Self::DB> {
        self.ectx.database()
    }
}
impl<'a, T: MainGroup> Deref for LCtx<'a, T> {
    type Target = ECtx<'a, T>;
    fn deref(&self) -> &ECtx<'a, T> {
        &self.ectx
    }
}
impl<'a, T: MainGroup> DerefMut for LCtx<'a, T> {
    fn deref_mut(&mut self) -> &mut ECtx<'a, T> {
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
}

impl Elab {
    pub fn low_ty_of<T: MainGroup>(&self, lctx: &mut LCtx<T>) -> Option<LowTy> {
        Some(match self {
            // We don't actually care what tag it is if it's not in a union
            Elab::Tag(_) => LowTy::Unit,
            Elab::Unit => LowTy::Unit,
            Elab::I32(_) => LowTy::Int(32),
            Elab::Var(x, ty) => {
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
            Elab::Fun(cl, v) => {
                if v.iter().any(|(args, _, ret)| {
                    !ret.is_concrete(lctx) || args.iter().any(|x| !x.is_concrete(lctx))
                }) {
                    // Don't lower this function yet, wait until it's called
                    return None;
                }

                if v.is_empty() {
                    panic!("Empty");
                }

                let mut cln = Cloner::new(lctx);
                let arg_tys = v.iter().fold(
                    (0..v.first().unwrap().0.len())
                        .map(|_| Vec::new())
                        .collect::<Vec<_>>(),
                    |mut acc, (from, _, _)| {
                        for (acc, from) in acc.iter_mut().zip(from.iter()) {
                            acc.push(from.cloned(&mut cln));
                        }
                        acc
                    },
                );

                let arg_tys: Vec<_> = arg_tys
                    .into_iter()
                    .map(|v| Elab::Union(v).whnf(lctx).simplify_unions(lctx))
                    .collect();

                let mut lctx = lctx.clone();
                lctx.add_clos(&cl);

                for (args, _, _) in v {
                    for (pat, ty) in args.iter().zip(&arg_tys) {
                        let pat = pat.cloned(&mut cln).whnf(&mut lctx);
                        pat.compile_match(&mut lctx, &mut Vec::new(), &ty, LowIR::Unit);
                    }
                }

                let ret_tys: Vec<_> = v
                    .iter()
                    .map(|(_, body, _)| body.cloned(&mut cln).low_ty_of(&mut lctx).unwrap())
                    .collect();
                let ret_ty = ret_tys.first().unwrap().clone();
                for i in ret_tys {
                    assert_eq!(i, ret_ty);
                }

                // Use the closure we already created for upvalues
                let upvalues: Vec<_> = cl
                    .tys
                    .iter()
                    .filter(|(_, t)| **t != Elab::Bottom)
                    .map(|(_, t)| t.cloned(&mut cln).whnf(&mut lctx).as_low_ty(&lctx))
                    .collect();

                // Now curry the arguments
                let arg_tys: Vec<_> = arg_tys.into_iter().map(|x| x.as_low_ty(&lctx)).collect();
                let mut i = arg_tys.len();
                arg_tys
                    .iter()
                    // .zip(&params)
                    .rfold(ret_ty, |ret_ty, arg_ty| {
                        // Thread parameters through closures as well
                        i -= 1;
                        let mut up = upvalues.clone();
                        up.extend(arg_tys.iter().take(i).cloned());
                        LowTy::ClosOwn {
                            from: Box::new(arg_ty.clone()),
                            to: Box::new(ret_ty),
                            upvalues: up,
                        }
                    })
            }
            Elab::App(f, x) => match f.get_type_rec(lctx) {
                Elab::Fun(_, _) => {
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
                        match s {
                            Elab::App(_, _) => return None,
                            s => s.low_ty_of(lctx)?,
                        }
                    }
                }
                Elab::App(_, _) => LowTy::Struct(vec![f.low_ty_of(lctx)?, x.low_ty_of(lctx)?]),
                // Ignore the tag if we have other data
                Elab::Tag(_) => x.low_ty_of(lctx)?,
                x => panic!(
                    "not function type: {}",
                    x.pretty(&lctx.bindings()).ansi_string()
                ),
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
            _ => panic!("ah"),
        })
    }

    /// Convert to LowIR, within the Salsa framework. Returns `None` if it's polymorphic
    ///
    /// Most work should be done here and not in `LowIR::codegen()`, since we want Salsa memoization
    pub fn as_low<T: MainGroup>(&self, lctx: &mut LCtx<T>) -> Option<LowIR> {
        Some(match self {
            // We don't actually care what tag it is if it's not in a union
            Elab::Tag(_) => LowIR::Unit,
            Elab::Unit => LowIR::Unit,
            Elab::I32(i) => LowIR::IntConst(unsafe { std::mem::transmute::<i32, u32>(*i) } as u64),
            Elab::Var(x, ty) => {
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
            Elab::Fun(cl, branches) => {
                if branches.iter().any(|(args, _, ret)| {
                    !ret.is_concrete(lctx) || args.iter().any(|x| !x.is_concrete(lctx))
                }) {
                    // Don't lower this function yet, wait until it's called
                    return None;
                }

                lctx.add_clos(cl);

                // A snapshot of the lctxironment, so we know what was defined before the arguments matched
                let lctx2 = lctx.clone();

                let mut cln = Cloner::new(lctx);
                let arg_tys = branches.iter().fold(
                    (0..branches.first().unwrap().0.len())
                        .map(|_| Vec::new())
                        .collect::<Vec<_>>(),
                    |mut acc, (from, _, _)| {
                        for (acc, from) in acc.iter_mut().zip(from.iter()) {
                            acc.push(from.cloned(&mut cln));
                        }
                        acc
                    },
                );

                let arg_tys: Vec<_> = arg_tys
                    .into_iter()
                    .map(|v| Elab::Union(v).whnf(lctx).simplify_unions(lctx))
                    .collect();

                // Compile the final body - do pattern matching etc.
                let block_ids: Vec<_> = (0..branches.len()).map(|_| next_block()).collect();
                let params: Vec<_> = (0..arg_tys.len())
                    .map(|i| lctx.bindings_mut().create(format!("_arg{}", i)))
                    .collect();
                let body = if let Elab::Union(variants) = arg_tys.first().unwrap() {
                    let tag = LowIR::Project(Box::new(LowIR::Local(params[0])), 0);
                    let payload = LowIR::Project(Box::new(LowIR::Local(params[0])), 1);
                    let payload_var = lctx.bindings_mut().create("_payload".to_string());

                    let mut cases: Vec<(BlockId, LowIR)> = Vec::new();
                    let mut phis: Vec<Vec<Phi>> = vec![Vec::new(); block_ids.len()];

                    // Switch on the incoming variant
                    for ty in variants.iter() {
                        // TODO cast payload_var to the right type

                        let block_id = next_block();

                        // TODO clone lctx if needed
                        let which_matched: Vec<(usize, LowIR)> = branches
                            .iter()
                            .enumerate()
                            // Only check the variants that could potentially match
                            .filter(|(_, (x, _, _))| x[0].overlap(&ty, &lctx2))
                            .map(|(i, (args, _, _))| {
                                let (arg, rest) = args.split_at(1);
                                let arg = &arg[0];

                                // If this branch matches a union, upcast to that union type
                                let param = match arg {
                                    Elab::Union(to) => if let Some((idx, _)) = to.iter().enumerate().find(|(_, x)| x.subtype_of(ty, lctx)) {
                                        LowIR::Variant(
                                            idx as u64,
                                            arg.as_low_ty(lctx),
                                            Box::new(LowIR::Local(payload_var))
                                        )
                                    } else {
                                        panic!("no union variant matched but it said it had overlap")
                                    }
                                    _ => LowIR::Local(payload_var),
                                };
                                // The rest of the arguments are currently matched just with ifs, not a switch
                                let mut need_phi = Vec::new();
                                let did_match = arg.compile_match(lctx, &mut need_phi, &arg_tys[0], param);
                                let did_match = rest.iter().enumerate().fold(did_match, |acc, (i, x)| {
                                    let x = x.compile_match(lctx, &mut need_phi, &arg_tys[i], LowIR::Local(params[i]));
                                    LowIR::BoolOp {
                                        op: BoolOp::And,
                                        lhs: Box::new(acc),
                                        rhs: Box::new(x),
                                    }
                                });
                                for (fresh, original) in need_phi {
                                    if let Some(phi) = phis[i].iter_mut().find(|x| x.result == original) {
                                        phi.incoming.push((block_id, fresh));
                                    } else {
                                        phis[i].push(Phi {
                                            incoming: vec![(block_id, fresh)],
                                            result: original
                                        });
                                    }
                                }
                                (i, did_match)
                            })
                            .collect();
                        // Right fold, since we go with the first matched pattern (left on top)
                        let case_block =
                            which_matched
                                .into_iter()
                                .rfold(LowIR::Unreachable, |acc, (i, x)| LowIR::If {
                                    cond: Box::new(x),
                                    yes: Box::new(LowIR::Branch(block_ids[i])),
                                    no: Box::new(acc),
                                });
                        cases.push((block_id, case_block));
                    }

                    assert_eq!(block_ids.len(), phis.len());

                    let blocks: Vec<_> = block_ids
                        .iter()
                        .copied()
                        .zip(phis)
                        .enumerate()
                        .map(|(i, (id, phis))| {
                            let body = &branches[i].1;
                            let body = body.as_low(lctx).unwrap();
                            (phis, id, body)
                        })
                        .collect();

                    let body = LowIR::MultiSwitch {
                        switch_on: Box::new(tag),
                        cases,
                        blocks,
                    };
                    LowIR::Let(payload_var, Box::new(payload), Box::new(body))
                } else {
                    let mut cln = Cloner::new(lctx);
                    // Not a union, so no switch, just pattern matching with ifs
                    branches
                        .iter()
                        .map(|(args, body, _)| {
                            // Skip upcasting to union, because if the argument was a union type we wouldn't be here

                            let mut need_phi = Vec::new();
                            let did_match = args.iter().enumerate().fold(
                                LowIR::BoolConst(true),
                                |acc, (i, x)| {
                                    let x = x.cloned(&mut cln).whnf(lctx);
                                    let x = x.compile_match(
                                        lctx,
                                        &mut need_phi,
                                        &arg_tys[i],
                                        LowIR::Local(params[i]),
                                    );
                                    LowIR::BoolOp {
                                        op: BoolOp::And,
                                        lhs: Box::new(acc),
                                        rhs: Box::new(x),
                                    }
                                },
                            );
                            // We're not going to use actual phis, so just rename the variables back
                            let body = need_phi.into_iter().fold(
                                body.cloned(&mut cln).as_low(lctx).unwrap(),
                                |body, (fresh, original)| {
                                    LowIR::Let(
                                        original,
                                        Box::new(LowIR::Local(fresh)),
                                        Box::new(body),
                                    )
                                },
                            );
                            (did_match, body)
                        })
                        // Right fold, since we go with the first matched pattern (left on top)
                        .rfold(LowIR::Unreachable, |acc, (did_match, body)| LowIR::If {
                            cond: Box::new(did_match),
                            // Inline branches (in LowIR) instead of putting them in blocks because they're not duplicated
                            yes: Box::new(body),
                            no: Box::new(acc),
                        })
                };

                // Use the closure we already created for upvalues
                let upvalues: Vec<_> = cl
                    .tys
                    .iter()
                    .filter(|(_, t)| **t != Elab::Bottom)
                    .map(|(k, t)| (*k, t.cloned(&mut cln).whnf(lctx).as_low_ty(lctx)))
                    .collect();

                // Now curry the arguments
                let arg_tys: Vec<_> = arg_tys.into_iter().map(|x| x.as_low_ty(lctx)).collect();
                let mut i = arg_tys.len();
                arg_tys
                    .iter()
                    .zip(&params)
                    .rfold(body, |body, (arg_ty, &arg_name)| {
                        // Thread parameters through closures as well
                        i -= 1;
                        let mut up = upvalues.clone();
                        up.extend(
                            params
                                .iter()
                                .zip(arg_tys.iter())
                                .take(i)
                                .map(|(x, y)| (*x, y.clone())),
                        );
                        LowIR::Closure {
                            fun_name: format!("$_closure{}", next_closure()),
                            attrs: Vec::new(),
                            arg_name,
                            arg_ty: arg_ty.clone(),
                            ret_ty: body.get_type(lctx),
                            body: Box::new(body),
                            upvalues: up,
                        }
                    })
            }
            Elab::App(f, x) => match f.get_type_rec(lctx) {
                Elab::Fun(cl, v) => {
                    lctx.add_clos(&cl);
                    let (mut args, _) = crate::elab::unionize_ty(v, lctx);
                    let from = args.remove(0);
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
                            Elab::Var(name, _) => {
                                if let Some((mono, ty)) = lctx.mono(*name, x) {
                                    return Some(LowIR::TypedGlobal(ty, mono));
                                } else {
                                    let s = self.cloned(&mut Cloner::new(&lctx)).whnf(lctx);
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
                                                        .chain(name.pretty(&lctx.bindings()))
                                                        .add("$")
                                                        .chain(x.pretty(&lctx.bindings()))
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
                                let s = self.cloned(&mut Cloner::new(&lctx)).whnf(lctx);
                                // Only recurse if it actually did something (it's not an App anymore)
                                match s {
                                    Elab::App(_, _) => return None,
                                    s => s.as_low(lctx)?,
                                }
                            }
                        }
                    }
                }
                Elab::App(_, _) => {
                    let fresh = lctx.bindings_mut().create("_".to_string());
                    LowIR::Struct(vec![(fresh, f.as_low(lctx)?), (fresh, f.as_low(lctx)?)])
                }
                // Ignore the tag if we have other data
                Elab::Tag(_) => x.as_low(lctx)?,
                x => panic!(
                    "not function type: {}",
                    x.pretty(&lctx.bindings()).ansi_string()
                ),
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
                            op: bu.int_op().unwrap(),
                            lhs: Box::new(LowIR::Local(a)),
                            rhs: Box::new(LowIR::Local(b)),
                        }),
                    }),
                }
            }
            // Type erasure
            Elab::Builtin(Builtin::Int) | Elab::Type(_) | Elab::Union(_) => LowIR::Unit,
            _ => panic!("{:?} not supported (ir)", self),
        })
    }

    /// Is this a concrete type, i.e., we don't need to monomorphize it?
    pub fn is_concrete<T: MainGroup>(&self, lctx: &LCtx<T>) -> bool {
        match self {
            Elab::Var(s, _) if lctx.database().elab(lctx.scope(), *s).is_some() => lctx
                .database()
                .elab(lctx.scope(), *s)
                .unwrap()
                .is_concrete(lctx),
            Elab::Var(s, _) if lctx.vals.contains_key(s) => lctx.val(*s).unwrap().is_concrete(lctx),
            Elab::Var(_, _) => false,
            Elab::Pair(x, y) => x.is_concrete(lctx) && y.is_concrete(lctx),
            Elab::StructInline(v) => v.iter().all(|(_, x)| x.is_concrete(lctx)),
            Elab::Type(_)
            | Elab::Unit
            | Elab::Builtin(_)
            | Elab::I32(_)
            | Elab::StructIntern(_)
            | Elab::Bottom
            | Elab::Tag(_) => true,
            Elab::Binder(_, t) => t.is_concrete(lctx),
            Elab::Fun(_, v) => v
                .iter()
                .all(|(a, b, _)| a.iter().all(|a| a.is_concrete(lctx)) && b.is_concrete(lctx)),
            Elab::Union(v) => v.iter().all(|x| x.is_concrete(lctx)),
            Elab::App(f, x) => f.is_concrete(lctx) && x.is_concrete(lctx),
            // This shouldn't happen unless the first param is neutral and thus not concrete
            Elab::Project(_, _) | Elab::Block(_) | Elab::Top => false,
        }
    }

    /// Convert a `Elab` representing a type to the `LowTy` that Elabs of that type are stored as
    pub fn as_low_ty<T: MainGroup>(&self, lctx: &LCtx<T>) -> LowTy {
        match self {
            Elab::Builtin(Builtin::Int) | Elab::I32(_) => LowTy::Int(32),
            Elab::Unit => LowTy::Unit,
            Elab::Binder(_, t) => t.as_low_ty(lctx),
            Elab::Fun(cl, v) => {
                let mut lctx = lctx.clone();
                lctx.add_clos(&cl);
                let mut cln = Cloner::new(&lctx);
                let (from, to) = crate::elab::unionize_ty(
                    v.iter()
                        .map(|(a, b, c)| {
                            (
                                a.iter()
                                    .map(|x| x.cloned(&mut cln).whnf(&mut lctx))
                                    .collect(),
                                b.cloned(&mut cln).whnf(&mut lctx),
                                c.cloned(&mut cln),
                            )
                        })
                        .collect(),
                    &lctx,
                );

                let to = to.as_low_ty(&lctx);

                from.into_iter().rfold(to, |ret, arg| {
                    let arg = arg.as_low_ty(&lctx);
                    LowTy::ClosRef {
                        from: Box::new(arg),
                        to: Box::new(ret),
                    }
                })
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
                Elab::Tag(_) => x.as_low_ty(lctx),
                Elab::App(_, _) => LowTy::Struct(vec![f.as_low_ty(lctx), x.as_low_ty(lctx)]),
                _ => panic!("{:?} is not supported", f),
            },
            Elab::Union(v) => LowTy::Union(v.iter().map(|x| x.as_low_ty(lctx)).collect()),
            // Type erasure
            Elab::Type(_) => LowTy::Unit,
            // We don't actually care what tag it is if it's not in a union
            Elab::Tag(_) => LowTy::Unit,
            _ => panic!(
                "{} is not supported",
                self.pretty(&lctx.bindings()).ansi_string()
            ),
        }
    }

    /// Compile this pattern to code that binds all binders and returns whether it matched
    ///
    /// This function clones `param`, so it should be a `LowIR::Local`
    fn compile_match<T: MainGroup>(
        &self,
        lctx: &mut LCtx<T>,
        // `(fresh var, original var)` so we can do `original = phi [fresh0 case0] [fresh1 case1]`
        need_phi: &mut Vec<(Sym, Sym)>,
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
                let fresh = lctx.bindings_mut().fresh(*x);
                let lty = t.as_low_ty(&lctx);
                lctx.set_low_ty(*x, lty.clone());
                lctx.set_low_ty(fresh, lty);
                need_phi.push((fresh, *x));
                LowIR::Let(
                    fresh,
                    Box::new(param.clone()),
                    Box::new(t.compile_match(lctx, need_phi, ty, param)),
                )
            }
            (Elab::Union(_), Elab::Union(_)) => {
                if self == ty {
                    LowIR::BoolConst(true)
                } else {
                    let param = param.cast(ty, self, lctx);
                    self.compile_match(lctx, need_phi, self, param)
                }
            }
            (Elab::Union(v), _) => {
                let (idx, t) = v
                    .iter()
                    .enumerate()
                    .find(|(_, x)| ty.subtype_of(x, lctx))
                    .unwrap();
                let param = LowIR::Variant(idx as u64, self.as_low_ty(lctx), Box::new(param));
                t.compile_match(lctx, need_phi, t, param)
            }
            (_, Elab::Union(v)) => {
                let tag = LowIR::Project(Box::new(param.clone()), 0);
                let tag_size = tag_width(v);
                let good_variant = v
                    .iter()
                    .enumerate()
                    .filter(|(_, x)| x.overlap(&self, lctx))
                    .fold(LowIR::BoolConst(false), |acc, (i, _)| LowIR::BoolOp {
                        op: BoolOp::Or,
                        lhs: Box::new(LowIR::CompOp {
                            op: CompOp::Eq,
                            lhs: Box::new(LowIR::SizedIntConst(tag_size, i as u64)),
                            rhs: Box::new(tag.clone()),
                        }),
                        rhs: Box::new(acc),
                    });
                let casted = param.cast(ty, self, lctx);
                let b = self.compile_match(lctx, need_phi, self, casted);
                LowIR::BoolOp {
                    op: BoolOp::And,
                    lhs: Box::new(good_variant),
                    rhs: Box::new(b),
                }
            }
            (Elab::StructIntern(i), _) => ScopeId::Struct(*i, Box::new(lctx.scope()))
                .inline(lctx)
                .compile_match(lctx, need_phi, ty, param),
            (Elab::StructInline(v), Elab::StructInline(tv)) => {
                let mut v: Vec<_> = v.iter().map(|(name, val)| (*name, val)).collect();
                v.sort_by_key(|(s, _)| s.raw());
                let mut tv: Vec<_> = tv.iter().map(|(name, val)| (*name, val)).collect();
                tv.sort_by_key(|(s, _)| s.raw());

                let mut body = LowIR::BoolConst(true);
                for (i, ((_name, val), (_, ty))) in v.into_iter().zip(tv).enumerate() {
                    let param = LowIR::Project(Box::new(param.clone()), i);
                    body = LowIR::BoolOp {
                        op: BoolOp::And,
                        lhs: Box::new(body),
                        rhs: Box::new(val.compile_match(lctx, need_phi, ty, param)),
                    };
                }
                body
            }
            (Elab::Pair(x, y), Elab::Pair(tx, ty)) => {
                let x_param = LowIR::Project(Box::new(param.clone()), 0);
                let y_param = LowIR::Project(Box::new(param), 1);
                let x = x.compile_match(lctx, need_phi, tx, x_param);
                let y = y.compile_match(lctx, need_phi, ty, y_param);
                LowIR::BoolOp {
                    op: BoolOp::And,
                    lhs: Box::new(x),
                    rhs: Box::new(y),
                }
            }
            (Elab::App(f, x), Elab::App(tf, tx)) => match &**f {
                Elab::Tag(_) => x.compile_match(lctx, need_phi, tx, param),
                Elab::App(_, _) => {
                    let f_param = LowIR::Project(Box::new(param.clone()), 0);
                    let x_param = LowIR::Project(Box::new(param), 1);
                    let f = f.compile_match(lctx, need_phi, tf, f_param);
                    let x = x.compile_match(lctx, need_phi, tx, x_param);
                    LowIR::BoolOp {
                        op: BoolOp::And,
                        lhs: Box::new(f),
                        rhs: Box::new(x),
                    }
                }
                _ => panic!("not a function"),
            },
            (Elab::I32(_), _) => LowIR::CompOp {
                op: CompOp::Eq,
                // This does the necessary bit-fiddling to make it a u64
                lhs: Box::new(self.as_low(lctx).unwrap()),
                rhs: Box::new(param),
            },
            // Don't bind anything
            // Once patterns can fail, these will be more interesting
            // TODO that
            (Elab::Type(_), _)
            | (Elab::Builtin(_), _)
            | (Elab::Unit, _)
            | (Elab::Tag(_), _)
            | (Elab::Fun(_, _), _) => LowIR::BoolConst(true),
            _ => panic!(
                "pattern {} can't be compiled yet",
                self.pretty(&lctx.bindings()).ansi_string()
            ),
        }
    }
}

/// Get the width of the smallest IntType that can differentiate between all the things in `v`
/// One of `i1, i8, i16, i32, i64`
pub fn tag_width<T>(v: &[T]) -> u32 {
    let l = v.len();
    if l <= 2 {
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

impl Builtin {
    fn int_op(self) -> Option<IntOp> {
        match self {
            Builtin::Add => Some(IntOp::Add),
            Builtin::Sub => Some(IntOp::Sub),
            Builtin::Mul => Some(IntOp::Mul),
            Builtin::Div => Some(IntOp::Div),
            _ => None,
        }
    }
}

impl LowIR {
    fn cast<T: MainGroup>(self, from: &Elab, to: &Elab, lctx: &mut LCtx<'_, T>) -> Self {
        match (from, to) {
            (cur, ty) if cur == ty => self,
            (_, Elab::Binder(_, t)) => self.cast(from, t, lctx),
            (Elab::Union(from), Elab::Union(vto)) => {
                let fresh = lctx.bindings_mut().create("union".to_string());
                let tag = LowIR::Project(Box::new(LowIR::Local(fresh)), 0);
                let mut cases: Vec<LowIR> = Vec::new();
                for ty in from.iter() {
                    if let Some((idx, _)) =
                        vto.iter().enumerate().find(|(_, x)| x.subtype_of(ty, lctx))
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
                for (i, t) in vto.iter().enumerate() {
                    if from.subtype_of(t, lctx) {
                        let r = self.cast(from, t, lctx);
                        return LowIR::Variant(i as u64, to.as_low_ty(lctx), Box::new(r));
                    }
                }
                panic!("none matched");
            }
            _ => self,
        }
    }

    pub fn borrow<T: MainGroup>(self, lctx: &LCtx<T>) -> Self {
        if let LowTy::ClosOwn { .. } = self.get_type(lctx) {
            LowIR::ClosureBorrow(Box::new(self))
        } else {
            self
        }
    }

    pub fn get_type<T: MainGroup>(&self, lctx: &LCtx<T>) -> LowTy {
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
            LowIR::Call(f, _) => match f.get_type(lctx) {
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
