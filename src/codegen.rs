//! We use Inkwell to generate LLVM.
//! Unfortunately, Inkwell is impossible to integrate with Salsa, for two reasons:
//! - Everything uses lifetimes, and Salsa currently doesn't support those *at all*
//! - Most things aren't thread safe, which Salsa requires
//! So, in Salsa, we convert terms into LowIR, which is supposed to be very close to LLVM.
//! We convert that into LLVM outside of Salsa, and hopefully that requires hardly any work - most should be done in Salsa.

use crate::{
    common::*,
    elab::{Elab, ElabStmt},
    term::Builtin,
};
pub use inkwell::context::Context;
use inkwell::{basic_block::BasicBlock, builder::Builder, module::Module, types::*, values::*};
use lazy_static::lazy_static;
use std::collections::HashMap;
use std::convert::{TryFrom, TryInto};
use std::sync::RwLock;

lazy_static! {
    static ref CLOSURE_NUM: RwLock<u32> = RwLock::new(0);
}
fn next_closure() -> u32 {
    let mut n = CLOSURE_NUM.write().unwrap();
    *n += 1;
    *n - 1
}

/// We need one of these to generate any LLVM code, but not to generate LowIR
pub struct CodegenCtx<'ctx> {
    context: &'ctx Context,
    builder: Builder<'ctx>,
    locals: HashMap<Sym, AnyValueEnum<'ctx>>,
}
impl<'ctx> CodegenCtx<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        CodegenCtx {
            context,
            builder: context.create_builder(),
            locals: HashMap::new(),
        }
    }
}

/// A LowIR type
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowTy {
    /// A 32-bit integers
    Int,
    /// A `void*` used for unknown closure environments. LLVM doesn't have `void*`, though, so it's really an `i8*`
    VoidPtr,
    /// Pika's `()` compiles to `{}`, nothing actually returns `void`
    Unit,
    /// A borrowed closure (the environment is essentially a `void*`), which you can call or pass as an argument
    ClosRef { from: Box<LowTy>, to: Box<LowTy> },
    /// An owned closure (with a known environment), which is mostly used for returning from functions
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
}
impl LowTy {
    /// The size of this type in bytes, on a 64-bit platform
    /// It doesn't need to be perfect, it's just used for finding the biggest type in a union
    fn size<'ctx>(&self, ctx: &'ctx Context) -> u64 {
        if let Some(size) = self
            .llvm(ctx)
            .size_of()
            .and_then(|x| x.get_zero_extended_constant())
        {
            return size;
        }
        let size = match self {
            LowTy::Int => 4,
            LowTy::VoidPtr => 8,
            LowTy::Unit => 0,
            LowTy::ClosRef { .. } => 16, // 8 for the fun ptr, 8 for the env ptr
            // Guessing at padding
            LowTy::ClosOwn { upvalues, .. } => {
                8 + upvalues
                    .iter()
                    .map(|x| {
                        let s = x.size(ctx);
                        if s == 0 {
                            0
                        } else {
                            s.max(8)
                        }
                    })
                    .sum::<u64>()
            }
            LowTy::Struct(v) => v.iter().map(|x| x.size(ctx).max(8)).sum(),
            // The tag is 8 bytes, because it would be anyway with padding
            LowTy::Union(v) => 8 + v.iter().map(|x| x.size(ctx)).max().unwrap(),
        };
        #[cfg(feature = "logging")]
        eprintln!("compiler warning: LLVM doesn't have a constant size for {:?}, guessing at size {} bytes", self, size);
        size
    }

    /// Create an LLVM function type that returns `self`
    fn llvm_fn_type<'ctx>(&self, ctx: &'ctx Context, oparams: &[LowTy]) -> FunctionType<'ctx> {
        let params: Vec<_> = oparams.iter().map(|x| x.llvm(ctx)).collect();
        let ret_ty = self.llvm(ctx);
        match ret_ty {
            BasicTypeEnum::ArrayType(t) => t.fn_type(&params, false),
            BasicTypeEnum::FloatType(t) => t.fn_type(&params, false),
            BasicTypeEnum::IntType(t) => t.fn_type(&params, false),
            BasicTypeEnum::PointerType(t) => t.fn_type(&params, false),
            BasicTypeEnum::StructType(t) => t.fn_type(&params, false),
            BasicTypeEnum::VectorType(t) => t.fn_type(&params, false),
        }
    }

    /// Get the LLVM representation of `self`
    fn llvm<'ctx>(&self, ctx: &'ctx Context) -> BasicTypeEnum<'ctx> {
        match self {
            LowTy::VoidPtr => ctx
                .i8_type()
                .ptr_type(inkwell::AddressSpace::Generic)
                .as_basic_type_enum(),
            LowTy::Int => ctx.i32_type().as_basic_type_enum(),
            LowTy::Unit => ctx.struct_type(&[], false).as_basic_type_enum(),
            LowTy::ClosRef { from, to } => {
                // Just use a pointer, since we don't know what we're actually passing
                let fun_ty = to.llvm_fn_type(ctx, &[LowTy::VoidPtr, (**from).clone()]);
                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                ctx.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        LowTy::VoidPtr.llvm(ctx).try_into().unwrap(),
                    ],
                    false,
                )
                .as_basic_type_enum()
            }
            LowTy::ClosOwn { from, to, upvalues } => {
                let env_struct_type = LowTy::Struct(upvalues.clone());
                let fun_ty = to.llvm_fn_type(ctx, &[LowTy::VoidPtr, (**from).clone()]);
                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                ctx.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        env_struct_type.llvm(ctx).try_into().unwrap(),
                    ],
                    false,
                )
                .as_basic_type_enum()
            }
            LowTy::Struct(v) => ctx
                .struct_type(
                    &v.iter()
                        .map(|a| a.llvm(ctx).try_into().unwrap())
                        .collect::<Vec<_>>(),
                    false,
                )
                .as_basic_type_enum(),
            LowTy::Union(v) => {
                let payload_type = v.iter().max_by_key(|x| x.size(ctx)).unwrap().llvm(ctx);
                // The tag is 8 bytes, because it probably would be anyway with padding
                let tag_type = ctx.i64_type().as_basic_type_enum();
                ctx.struct_type(&[tag_type, payload_type], false)
                    .as_basic_type_enum()
            }
        }
    }
}
impl Elab {
    fn has_type(&self) -> bool {
        match self {
            Elab::Pair(x, y) => x.has_type() || y.has_type(),
            Elab::StructInline(v) => v.iter().any(|(_, x)| x.has_type()),
            Elab::Union(v) => v.iter().any(|x| x.has_type()),
            Elab::Type => true,
            Elab::Unit | Elab::Builtin(_) | Elab::I32(_) | Elab::Var(_, _) | Elab::Tag(_) => false,
            Elab::Binder(_, t) => t.has_type(),
            Elab::Fun(a, b, _) => a.has_type() || b.has_type(),
            Elab::App(_, _) | Elab::Project(_, _) | Elab::Block(_) | Elab::StructIntern(_) => false,
        }
    }

    pub fn is_polymorphic(&self) -> bool {
        match self {
            Elab::Pair(x, y) => x.is_polymorphic() || y.is_polymorphic(),
            Elab::StructInline(v) => v.iter().any(|(_, x)| x.has_type()),
            Elab::Union(v) => v.iter().any(|x| x.is_polymorphic()),
            Elab::Type
            | Elab::Unit
            | Elab::Builtin(_)
            | Elab::I32(_)
            | Elab::Var(_, _)
            | Elab::Tag(_) => false,
            Elab::Binder(_, t) => t.has_type(),
            Elab::Fun(a, b, _) => a.is_polymorphic() || b.is_polymorphic(),
            Elab::App(_, _) | Elab::Project(_, _) | Elab::Block(_) | Elab::StructIntern(_) => false,
        }
    }

    /// Is this a concrete type, i.e., we don't need to monomorphize it?
    pub fn is_concrete<T: MainGroup>(&self, env: &TempEnv<T>) -> bool {
        match self {
            Elab::Var(s, _) if env.db.elab(env.scope(), *s).is_some() => env.db.elab(env.scope(), *s).unwrap().is_concrete(env),
            Elab::Var(s, _) if env.vals.contains_key(s) => env.val(*s).unwrap().is_concrete(env),
            Elab::Var(_, _) => false,
            Elab::Pair(x, y) => x.is_concrete(env) && y.is_concrete(env),
            Elab::StructInline(v) => v.iter().all(|(_, x)| x.is_concrete(env)),
            Elab::Type
            | Elab::Unit
            | Elab::Builtin(_)
            // Not a type, but concrete, I guess? this should be unreachable
            | Elab::I32(_)
            | Elab::StructIntern(_)
            | Elab::Tag(_) => true,
            Elab::Binder(_, t) => t.is_concrete(env),
            Elab::Fun(a, b, _) => a.is_concrete(env) && b.is_concrete(env),
            Elab::Union(v) => v.iter().all(|x| x.is_concrete(env)),
            Elab::App(f, x) => f.is_concrete(env) && x.is_concrete(env),
            // This shouldn't happen unless the first param is neutral and thus not concrete
            Elab::Project(_, _)
            | Elab::Block(_) => false,
        }
    }

    /// Convert a `Elab` representing a type to the `LowTy` that Elabs of that type are stored as
    pub fn as_low_ty(&self) -> LowTy {
        match self {
            Elab::Builtin(Builtin::Int) => LowTy::Int,
            Elab::Unit => LowTy::Unit,
            Elab::Binder(_, t) => t.as_low_ty(),
            Elab::Fun(from, to, _) => LowTy::ClosRef {
                from: Box::new(from.as_low_ty()),
                to: Box::new(to.as_low_ty()),
            },
            Elab::Pair(a, b) => LowTy::Struct(vec![a.as_low_ty(), b.as_low_ty()]),
            Elab::StructInline(v) => {
                let mut v: Vec<_> = v.iter().collect();
                v.sort_by_key(|(x, _)| x.raw());
                LowTy::Struct(v.into_iter().map(|(_, v)| v.as_low_ty()).collect())
            }
            // Attach data to tags
            Elab::App(f, x) => match &**f {
                // Ignore the tag
                Elab::Tag(_) => x.as_low_ty(),
                Elab::App(_, _) => LowTy::Struct(vec![f.as_low_ty(), x.as_low_ty()]),
                _ => panic!("{:?} is not supported", f),
            },
            Elab::Union(v) => LowTy::Union(v.iter().map(|x| x.as_low_ty()).collect()),
            // Type erasure
            Elab::Type => LowTy::Unit,
            // We don't actually care what tag it is if it's not in a union
            Elab::Tag(_) => LowTy::Unit,
            _ => panic!("{:?} is not supported", self),
        }
    }
}

impl Elab {
    /// Compile this pattern to code that binds all binders and runs `body`
    /// Currently it's unconditional, so pattern matching can't fail
    ///
    /// This function clones `param`, so it should be a `LowIR::Local`
    fn compile_match<T: MainGroup>(
        &self,
        env: &mut TempEnv<T>,
        param: LowIR,
        body: LowIR,
    ) -> LowIR {
        match self {
            Elab::Binder(x, _) => LowIR::Let(*x, Box::new(param), Box::new(body)),
            Elab::StructIntern(i) => ScopeId::Struct(*i, Box::new(env.scope()))
                .inline(env.db)
                .compile_match(env, param, body),
            Elab::StructInline(v) => {
                let mut v: Vec<_> = v.iter().map(|(name, val)| (*name, val)).collect();
                v.sort_by_key(|(s, _)| s.raw());
                let mut body = body;
                for (i, (_name, val)) in v.into_iter().enumerate() {
                    let param = LowIR::Project(Box::new(param.clone()), i);
                    body = val.compile_match(env, param, body);
                }
                body
            }
            Elab::Pair(f, x) => {
                let f_param = LowIR::Project(Box::new(param.clone()), 0);
                let x_param = LowIR::Project(Box::new(param), 1);
                let f = f.compile_match(env, f_param, body);
                x.compile_match(env, x_param, f)
            }
            Elab::App(f, x) => match &**f {
                Elab::Tag(_) => x.compile_match(env, param, body),
                Elab::App(_, _) => {
                    let f_param = LowIR::Project(Box::new(param.clone()), 0);
                    let x_param = LowIR::Project(Box::new(param), 1);
                    let f = f.compile_match(env, f_param, body);
                    x.compile_match(env, x_param, f)
                }
                _ => panic!("not a function"),
            },
            // Don't bind anything
            // Once patterns can fail, these will be more interesting
            Elab::Type
            | Elab::Builtin(_)
            | Elab::Unit
            | Elab::Tag(_)
            | Elab::Fun(_, _, _)
            | Elab::Union(_) => body,
            _ => panic!(
                "pattern {} can't be compiled yet",
                self.pretty(&env.bindings()).ansi_string()
            ),
        }
    }

    /// Convert to LowIR, within the Salsa framework. Returns `None` if it's polymorphic
    ///
    /// Most work should be done here and not in `LowIR::codegen()`, since we want Salsa memoization
    pub fn as_low<T: MainGroup>(&self, env: &mut TempEnv<T>) -> Option<LowIR> {
        Some(match self {
            // Type erasure
            _ if self.get_type(env) == Elab::Type => LowIR::Unit,
            // We don't actually care what tag it is if it's not in a union
            Elab::Tag(_) => LowIR::Unit,
            Elab::Unit => LowIR::Unit,
            Elab::I32(i) => LowIR::IntConst(unsafe { std::mem::transmute::<i32, u32>(*i) } as u64),
            Elab::Var(x, ty) => {
                if ty.is_concrete(env)
                    && env.db.low_fun(env.scope.clone(), *x) != Err(LowError::Polymorphic)
                {
                    return env
                        .db
                        .mangle(env.scope.clone(), *x)
                        .map(|s| LowIR::Global(*x, env.scope(), s))
                        .or_else(|| {
                            if env.tys.contains_key(x) {
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
                let a = a.as_low(env)?;
                let b = b.as_low(env)?;
                let fresh = env.bindings_mut().create("_".to_string());
                LowIR::Struct(vec![(fresh, a), (fresh, b)])
            }
            // We compile records in either "module mode" or "struct mode"
            // Inline structs (ones that weren't in the original code) are always compiled in struct mode
            // Interned structs (ones that were in the original code) are compiled in struct mode if they use local variables
            // Otherwise, they're compiled in module mode
            Elab::StructInline(iv) => {
                let mut rv = Vec::new();
                for (name, val) in iv {
                    let ty = val.get_type(env);
                    env.set_ty(*name, ty);
                    rv.push((*name, val.as_low(env)?));
                }
                rv.sort_by_key(|(x, _)| x.raw());
                LowIR::Struct(rv)
            }
            Elab::StructIntern(id) => {
                let scope = ScopeId::Struct(*id, Box::new(env.scope()));

                if env.tys.keys().any(|t| self.uses(*t, env)) {
                    // Uses local variables, so we can't make its members globals
                    return scope.inline(env.db).as_low(env);
                }

                // Compile it in "module mode": all members are global functions, like top-level definitions
                let mut rv = Vec::new();
                let s = env.db.symbols(scope.clone());
                for name in s.iter() {
                    match env.db.low_fun(scope.clone(), **name) {
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
                            let ty = val.get_type(env);
                            env.set_ty(*name, ty);
                            let val = val.as_low(env)?;
                            (*name, val)
                        }),
                    })
                    .collect();
                let last = match v.last().unwrap() {
                    ElabStmt::Expr(e) => e.as_low(env)?,
                    ElabStmt::Def(_, _) => LowIR::Unit,
                };
                lows.into_iter().rfold(last, |acc, (name, val)| {
                    LowIR::Let(name, Box::new(val), Box::new(acc))
                })
            }
            Elab::Fun(arg, body, ret_ty) => {
                if !ret_ty.is_concrete(env) || !arg.is_concrete(env) {
                    // Don't lower this function yet, wait until it's called
                    return None;
                }

                let upvalues: Vec<_> = env
                    .tys
                    .iter()
                    .filter(|(s, _)| body.uses(**s, env))
                    .map(|(s, t)| (*s, t.as_low_ty()))
                    .collect();

                let mut env = env.clone();
                let mut pat = arg.cloned(&mut env);
                pat.normal(&mut env);

                pat.match_types(&pat, &mut env);

                let fresh = env.bindings_mut().create("_arg".to_string());
                let param = LowIR::Local(fresh);
                // This `cloned` applies the renames from the `arg.cloned()` up there ^
                let body = body.cloned(&mut env).as_low(&mut env)?;
                let body = pat.compile_match(&mut env, param, body);

                let ret_ty = body.get_type(&env);
                LowIR::Closure {
                    fun_name: format!("$_closure{}", next_closure()),
                    arg_name: fresh,
                    arg_ty: pat.as_low_ty(),
                    ret_ty,
                    body: Box::new(body),
                    upvalues,
                }
            }
            Elab::App(f, x) => match f.get_type(env) {
                Elab::Fun(mut from, _, _) => {
                    // In case it has variables etc.
                    from.normal(env);
                    if from.is_polymorphic() {
                        match &**f {
                            Elab::Var(name, _) => {
                                if let Some((mono, ty)) = env.mono(*name, x) {
                                    return Some(LowIR::TypedGlobal(ty, mono));
                                } else {
                                    let mut s = self.cloned(&mut env.clone());
                                    // Only recurse if it actually did something
                                    if s.whnf(env) {
                                        let mut low = s.as_low(env)?;
                                        let ty = low.get_type(env);
                                        match &mut low {
                                            LowIR::Closure {
                                                fun_name, upvalues, ..
                                            } if upvalues.is_empty() => {
                                                *fun_name = Doc::start("$mono$")
                                                    .chain(name.pretty(&env.bindings()))
                                                    .add("$")
                                                    .chain(x.pretty(&env.bindings()))
                                                    .raw_string();
                                                env.set_mono(
                                                    *name,
                                                    x.cloned(&mut env.clone()),
                                                    fun_name.to_string(),
                                                    ty,
                                                );
                                            }
                                            _ => (),
                                        };
                                        return Some(low);
                                    }
                                }
                            }
                            _ => {
                                // Inline it
                                let mut s = self.cloned(&mut env.clone());
                                // Only recurse if it actually did something
                                if s.whnf(env) {
                                    return s.as_low(env);
                                }
                            }
                        }
                    }
                    // We borrow both the function and the argument
                    let f = f.as_low(env)?.borrow(env);
                    let x = x.as_low(env)?.cast(from.as_low_ty(), env).unwrap();
                    LowIR::Call(Box::new(f), Box::new(x))
                }
                Elab::App(_, _) => {
                    let fresh = env.bindings_mut().create("_".to_string());
                    LowIR::Struct(vec![(fresh, f.as_low(env)?), (fresh, f.as_low(env)?)])
                }
                // Ignore the tag if we have other data
                Elab::Tag(_) => x.as_low(env)?,
                _ => panic!("not function type"),
            },
            Elab::Project(r, m) => {
                let ty = r.get_type(env);
                let mut list: Vec<_> = match ty {
                    Elab::StructIntern(id) => {
                        let scope = ScopeId::Struct(id, Box::new(env.scope()));
                        env.db
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
                let r = r.as_low(env)?;
                LowIR::Project(Box::new(r), idx)
            }
            _ => panic!("{:?} not supported (ir)", self),
        })
    }
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

/// An expression in LowIR
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LowIR {
    Unit,
    IntConst(u64),
    IntOp {
        op: IntOp,
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
    /// Wraps an owned closure and turns it into a borrowed one (takes a pointer to the environment and bitcasts it to `void*`)
    ClosureBorrow(Box<LowIR>),
    /// An owned closure
    Closure {
        fun_name: String,
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
    Call(Box<LowIR>, Box<LowIR>),
}

impl LowIR {
    pub fn cast<T: MainGroup>(self, ty: LowTy, env: &mut TempEnv<'_, T>) -> Result<Self, Self> {
        let cur = self.get_type(env);
        match (cur, ty) {
            (cur, ty) if cur == ty => Ok(self),
            (LowTy::Union(from), LowTy::Union(to)) => {
                let fresh = env.bindings_mut().create("union".to_string());
                let tag = LowIR::Project(Box::new(LowIR::Local(fresh)), 0);
                let mut cases: Vec<LowIR> = Vec::new();
                for ty in from.iter() {
                    if let Some((idx, _)) = to.iter().enumerate().find(|(_, x)| *x == ty) {
                        cases.push(LowIR::Variant(
                            idx as u64,
                            LowTy::Union(to.clone()),
                            Box::new(LowIR::Local(fresh)),
                        ));
                    } else {
                        return Err(self);
                    }
                }
                Ok(LowIR::Let(
                    fresh,
                    Box::new(self),
                    Box::new(LowIR::Switch(Box::new(tag), cases)),
                ))
            }
            (_, LowTy::Union(to)) => {
                let mut s = self;
                for (i, t) in to.iter().enumerate() {
                    match s.cast(t.clone(), env) {
                        Ok(r) => {
                            return Ok(LowIR::Variant(i as u64, LowTy::Union(to), Box::new(r)))
                        }
                        Err(back) => s = back,
                    }
                }
                Err(s)
            }
            (
                LowTy::ClosOwn { to, from, .. },
                LowTy::ClosRef {
                    to: to2,
                    from: from2,
                },
            ) if to == to2 && from == from2 => Ok(LowIR::ClosureBorrow(Box::new(self))),
            _ => Err(self),
        }
    }

    pub fn borrow<T: MainGroup>(self, env: &TempEnv<T>) -> Self {
        if let LowTy::ClosOwn { .. } = self.get_type(env) {
            LowIR::ClosureBorrow(Box::new(self))
        } else {
            self
        }
    }

    pub fn get_type<T: MainGroup>(&self, env: &TempEnv<T>) -> LowTy {
        match self {
            LowIR::Unit => LowTy::Unit,
            LowIR::IntConst(_) => LowTy::Int,
            LowIR::IntOp { .. } => LowTy::Int,
            LowIR::Struct(v) => LowTy::Struct(v.iter().map(|(_, x)| x.get_type(env)).collect()),
            LowIR::Project(v, i) => {
                if let LowTy::Struct(v) = v.get_type(env) {
                    v[*i].clone()
                } else {
                    panic!("Not a struct type on project")
                }
            }
            LowIR::Let(_, _, body) => body.get_type(env),
            LowIR::Local(s) => env
                .ty(*s)
                .unwrap_or_else(|| panic!("not found: {}", s.pretty(&env.bindings()).ansi_string()))
                .cloned(&mut env.clone())
                .as_low_ty(),
            LowIR::TypedGlobal(t, _) => t.clone(),
            LowIR::Global(s, scope, _) => env.db.low_fun(scope.clone(), *s).unwrap().ret_ty,
            LowIR::Call(f, _) => match f.get_type(env) {
                LowTy::ClosRef { to, .. } | LowTy::ClosOwn { to, .. } => *to,
                _ => panic!("not a function LowTy"),
            },
            LowIR::ClosureBorrow(c) => {
                if let LowTy::ClosOwn { to, from, .. } = c.get_type(env) {
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
            LowIR::Switch(_, v) => v.first().unwrap().get_type(env),
        }
    }

    /// Convert this expression into an LLVM Elab
    ///
    /// Should be really simple, complex things belong in STerm::as_low
    fn codegen<'ctx>(
        &self,
        ctx: &mut CodegenCtx<'ctx>,
        module: &Module<'ctx>,
    ) -> AnyValueEnum<'ctx> {
        match self {
            LowIR::Unit => ctx
                .context
                .struct_type(&[], false)
                .const_named_struct(&[])
                .into(),
            LowIR::IntConst(i) => ctx.context.i32_type().const_int(*i, false).into(),
            LowIR::IntOp { op, lhs, rhs } => {
                let lhs = lhs.codegen(ctx, module).into_int_value();
                let rhs = rhs.codegen(ctx, module).into_int_value();
                match op {
                    IntOp::Add => ctx.builder.build_int_add(lhs, rhs, "add"),
                    IntOp::Sub => ctx.builder.build_int_sub(lhs, rhs, "sub"),
                }
                .into()
            }
            LowIR::Struct(v) => {
                let values: Vec<BasicValueEnum> = v
                    .iter()
                    .map(|(n, x)| {
                        let v = x.codegen(ctx, module);
                        ctx.locals.insert(*n, v);
                        v.try_into().unwrap()
                    })
                    .collect();
                let types: Vec<_> = values.iter().map(|x| x.get_type()).collect();
                let mut struct_val = ctx
                    .context
                    .struct_type(&types, false)
                    .get_undef()
                    .as_aggregate_value_enum();
                for (i, v) in values.into_iter().enumerate() {
                    struct_val = ctx
                        .builder
                        .build_insert_value(struct_val, v, i as u32, "struct")
                        .unwrap();
                }
                struct_val.as_any_value_enum()
            }
            LowIR::Project(r, m) => {
                let r = r.codegen(ctx, module).into_struct_value();
                ctx.builder
                    .build_extract_value(r, *m as u32, "project")
                    .unwrap()
                    .as_any_value_enum()
            }
            LowIR::Let(var, val, body) => {
                let val = val.codegen(ctx, module);
                ctx.locals.insert(*var, val);
                body.codegen(ctx, module)
            }
            LowIR::Local(var) => *ctx.locals.get(var).expect("Used nonexistent local"),
            LowIR::Global(_, _, name) => ctx
                .builder
                .build_call(module.get_function(name).unwrap(), &[], name)
                .as_any_value_enum(),
            LowIR::TypedGlobal(ty, name) => {
                let ty = LowTy::Struct(vec![ty.clone(), LowTy::Unit])
                    .llvm(&ctx.context)
                    .into_struct_type();

                let fun = module.get_function(name).unwrap();
                let fun_ptr = fun.as_any_value_enum().into_pointer_value();

                ctx.builder
                    .build_insert_value(ty.get_undef(), fun_ptr, 0, "clos")
                    .unwrap()
                    .as_any_value_enum()
            }
            LowIR::Closure {
                fun_name,
                arg_name,
                arg_ty,
                body,
                ret_ty,
                upvalues,
            } => {
                let env_values: Vec<_> = upvalues
                    .iter()
                    .map(|(n, _)| {
                        BasicValueEnum::try_from(*ctx.locals.get(n).expect("Upvalue doesn't exist"))
                            .unwrap()
                    })
                    .collect();
                let env_types: Vec<_> = upvalues.iter().map(|(_, t)| t.clone()).collect();
                let env_struct_type = LowTy::Struct(env_types);
                let mut env_struct = env_struct_type
                    .llvm(&ctx.context)
                    .into_struct_type()
                    .get_undef()
                    .as_aggregate_value_enum();
                for (i, v) in env_values.into_iter().enumerate() {
                    env_struct = ctx
                        .builder
                        .build_insert_value(env_struct, v, i as u32, "struct")
                        .unwrap();
                }

                let bb = ctx.builder.get_insert_block().unwrap();

                let fun_ty = ret_ty.llvm_fn_type(&ctx.context, &[LowTy::VoidPtr, arg_ty.clone()]);
                let fun = module.add_function(&fun_name, fun_ty, None);
                let entry = ctx.context.append_basic_block(fun, "entry");
                ctx.builder.position_at_end(entry);

                let mut old_locals = HashMap::new();
                std::mem::swap(&mut old_locals, &mut ctx.locals);
                ctx.locals
                    .insert(*arg_name, fun.get_last_param().unwrap().as_any_value_enum());
                // Add upvalues to local environment
                let local_env = fun.get_first_param().unwrap().into_pointer_value();
                let local_env = ctx
                    .builder
                    .build_bitcast(
                        local_env,
                        env_struct_type
                            .llvm(&ctx.context)
                            .into_struct_type()
                            .ptr_type(inkwell::AddressSpace::Generic),
                        "env",
                    )
                    .into_pointer_value();
                let local_env = ctx
                    .builder
                    .build_load(local_env, "local_env")
                    .into_struct_value();
                for (i, (name, _)) in upvalues.iter().enumerate() {
                    let val = ctx
                        .builder
                        .build_extract_value(local_env, i as u32, "$_upvalue")
                        .unwrap();
                    ctx.locals.insert(*name, val.as_any_value_enum());
                }

                let body: BasicValueEnum = body.codegen(ctx, module).try_into().unwrap();
                ctx.builder.build_return(Some(&body as &_));

                // Go back to the original function
                std::mem::swap(&mut old_locals, &mut ctx.locals);
                ctx.builder.position_at_end(bb);

                let fun_ptr_ty = fun_ty.ptr_type(inkwell::AddressSpace::Generic);
                let clos_ty = ctx.context.struct_type(
                    &[
                        fun_ptr_ty.as_basic_type_enum(),
                        env_struct_type.llvm(&ctx.context),
                    ],
                    false,
                );
                // Magic, might break eventually
                let fun_ptr = fun.as_any_value_enum().into_pointer_value();
                let closure = clos_ty.get_undef();
                let closure = ctx
                    .builder
                    .build_insert_value(closure, fun_ptr, 0, "clos.partial")
                    .unwrap();
                let closure = ctx
                    .builder
                    .build_insert_value(closure, env_struct, 1, "clos")
                    .unwrap();
                closure.as_any_value_enum()
            }
            LowIR::ClosureBorrow(f) => {
                // Extract the function pointer and environment from the closure
                let f_struct = f.codegen(ctx, module).into_struct_value();
                let f_ptr = ctx
                    .builder
                    .build_extract_value(f_struct, 0, "fun")
                    .unwrap()
                    .into_pointer_value();
                let f_rest = ctx.builder.build_extract_value(f_struct, 1, "env").unwrap();
                let rest_ptr = ctx.builder.build_alloca(f_rest.get_type(), "env_ptr");
                ctx.builder.build_store(rest_ptr, f_rest);
                let void_ptr_ty =
                    BasicTypeEnum::try_from(LowTy::VoidPtr.llvm(&ctx.context)).unwrap();
                let rest_ptr = ctx.builder.build_bitcast(rest_ptr, void_ptr_ty, "env_cast");

                // Create a new struct
                let ref_type = ctx
                    .context
                    .struct_type(&[f_ptr.get_type().as_basic_type_enum(), void_ptr_ty], false);
                let closure_ref = ref_type.get_undef();
                let closure_ref = ctx
                    .builder
                    .build_insert_value(closure_ref, f_ptr, 0, "clos_ref.partial")
                    .unwrap();
                let closure_ref = ctx
                    .builder
                    .build_insert_value(closure_ref, rest_ptr, 1, "clos_ref")
                    .unwrap();
                closure_ref.as_any_value_enum()
            }
            LowIR::Call(f, x) => {
                let x = x.codegen(ctx, module).try_into().unwrap();

                // Extract the function pointer and environment from the closure
                // We're calling a borrowed closure, so it has a pointer to the environment already
                let f_struct = f.codegen(ctx, module).into_struct_value();
                let f_ptr = ctx
                    .builder
                    .build_extract_value(f_struct, 0, "fun")
                    .unwrap()
                    .into_pointer_value();
                let f_rest = ctx.builder.build_extract_value(f_struct, 1, "env").unwrap();

                ctx.builder
                    .build_call(f_ptr, &[f_rest, x], "call")
                    .as_any_value_enum()
            }
            LowIR::Variant(tag, ty, val) => {
                let ty = ty.llvm(&ctx.context).into_struct_type();
                let payload_type = ty.get_field_type_at_index(1).unwrap();

                let tag = ctx.context.i64_type().const_int(*tag, false);
                let val: BasicValueEnum = val.codegen(ctx, module).try_into().unwrap();
                let val_ty = val.get_type();
                let val_ptr = ctx.builder.build_alloca(val_ty, "payload_ptr");
                ctx.builder.build_store(val_ptr, val);
                let val_ptr = ctx
                    .builder
                    .build_bitcast(
                        val_ptr,
                        payload_type.ptr_type(inkwell::AddressSpace::Generic),
                        "payload_ptr_cast",
                    )
                    .into_pointer_value();
                // This reads some unititialized memory, but it's on the stack so it's not going to segfault, and it never uses the value so it's fine
                let val = ctx.builder.build_load(val_ptr, "payload");

                let ret = ty.get_undef();
                let ret = ctx
                    .builder
                    .build_insert_value(ret, tag, 0, "with_tag")
                    .unwrap();
                let ret = ctx
                    .builder
                    .build_insert_value(ret, val, 1, "with_val")
                    .unwrap();
                ret.as_any_value_enum()
            }
            LowIR::Switch(tag, cases) => {
                let tag = tag.codegen(ctx, module).into_int_value();

                let cur_block = ctx.builder.get_insert_block().unwrap();
                let blocks: Vec<(IntValue, BasicBlock)> = cases
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        (
                            ctx.context.i64_type().const_int(i as u64, false),
                            ctx.context
                                .insert_basic_block_after(cur_block, &format!("case.{}", i)),
                        )
                    })
                    .collect();
                let else_block = ctx.context.insert_basic_block_after(
                    blocks.first().map(|(_, x)| *x).unwrap_or(cur_block),
                    "_catchall",
                );
                let _switch = ctx.builder.build_switch(tag, else_block, &blocks);

                // Mark the else block as unreachable
                ctx.builder.position_at_end(else_block);
                ctx.builder.build_unreachable();

                let after_block = ctx.context.insert_basic_block_after(else_block, "merge");

                // Only execute the branch code in its branch, then use a phi to merge them back together
                let mut ty = ctx.context.i32_type().as_basic_type_enum();
                let mut phis: Vec<(BasicValueEnum, BasicBlock)> = Vec::new();
                for ((_, block), val) in blocks.into_iter().zip(cases) {
                    ctx.builder.position_at_end(block);
                    let val = val.codegen(ctx, module);
                    ty = val.get_type().try_into().unwrap();
                    phis.push((BasicValueEnum::try_from(val).unwrap(), block));
                    ctx.builder.build_unconditional_branch(after_block);
                }

                ctx.builder.position_at_end(after_block);
                let phi = ctx.builder.build_phi(ty, "phi");
                let phis_dyn: Vec<(&dyn BasicValue, BasicBlock)> =
                    phis.iter().map(|(x, y)| (x as &_, *y)).collect();
                phi.add_incoming(&phis_dyn);

                phi.as_any_value_enum()
            }
        }
    }
}

/// An integer math operation. Currently not supported in the main language
#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum IntOp {
    Add,
    Sub,
}

impl LowFun {
    /// Add the function definition represented by this `LowFun` to the passed LLVM `Module`
    fn codegen<'ctx>(&self, ctx: &mut CodegenCtx<'ctx>, module: &Module<'ctx>) {
        let fun = module.add_function(
            &self.name,
            self.ret_ty.llvm_fn_type(&ctx.context, &[]),
            None,
        );
        let entry = ctx.context.append_basic_block(fun, "entry");
        ctx.builder.position_at_end(entry);
        let ret_val: BasicValueEnum = self.body.codegen(ctx, module).try_into().unwrap();
        ctx.builder.build_return(Some(&ret_val as &_));
    }
}

impl LowMod {
    /// Convert this `LowMod` into an LLVM `Module`
    pub fn codegen<'ctx>(&self, ctx: &mut CodegenCtx<'ctx>) -> Module<'ctx> {
        let module = ctx.context.create_module(&self.name);
        for i in self.funs.iter() {
            i.codegen(ctx, &module);
        }
        module
    }
}
