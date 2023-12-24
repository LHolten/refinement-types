#![allow(dead_code)]

use std::marker::PhantomData;
use std::rc::{Rc, Weak};
use std::{fmt::Debug, ops::Deref};

pub mod builtin;
pub mod eval;
pub mod func_term;
pub mod heap;
mod subtyp;
pub mod term;
pub mod typing;
mod verify;

use miette::{Diagnostic, SourceSpan};

use crate::desugar::Desugar;
use crate::parse;

use self::func_term::FuncTerm;
use self::heap::{ConsumeErr, Heap};

use self::builtin::Builtin;
use self::term::Term;
use self::verify::Assume;

// Side effect free expression
#[derive(Clone)]
pub enum Free<T> {
    BinOp {
        l: Rc<Free<T>>,
        r: Rc<Free<T>>,
        op: BinOp,
    },
    Just(i64, u32),
    Var(T),
}

#[derive(Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Div,
    Mul,
    Rem,
    Eq,
    Less,
    LessEq,
    NotEq,
    And,
    MulSafe,
    Shl,
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct Cond {
    pub named: Name,
    // only if the cond is `true`, does this named resource exist
    pub cond: Term,
    // these are the arguments to the named resource
    pub args: Vec<Term>,
    pub span: SourceSpan,
}

#[derive(Clone)]
pub struct Switch {
    pub resource: Resource,
    pub args: Vec<Term>,
    pub cond: Term,
    pub span: Option<SourceSpan>,
}

/// a single resource
#[derive(Clone)]
pub enum Resource {
    Named(Name),
    Owned,
}

#[derive(Clone)]
pub struct Forall {
    pub resource: Resource,
    // mask specifies where is valid
    pub mask: FuncTerm,
    pub span: Option<SourceSpan>,
}

#[derive(Clone)]
pub struct CtxForall {
    pub have: Forall,
    pub value: FuncTerm,
}

impl Debug for CtxForall {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let idx = self.have.make_fresh_args();
        let mask = self.have.mask.apply_bool(&idx);
        write!(f, "{mask:?}")
    }
}

#[derive(Clone, Default)]
#[must_use]
pub struct SubContext {
    assume: Assume,
    forall: Vec<CtxForall>,
    // these do not have to exist, but might
    hints: Vec<Hint>,
}

#[derive(Clone)]
pub struct Hint {
    id: usize,
    args: Vec<Term>,
}

pub struct PosTyp;

pub struct NegTyp {
    pub arg: PosTyp,
    pub ret: Fun<PosTyp>,
}

impl NegTyp {
    pub fn new(ret: Fun<PosTyp>) -> Self {
        NegTyp { arg: PosTyp, ret }
    }
}

#[allow(clippy::type_complexity)]
pub struct Fun<T> {
    // the arguments that are expected to be in scope
    pub tau: Vec<(u32, String)>,
    pub span: Option<SourceSpan>,
    pub fun: Rc<dyn Fn(&mut dyn Heap, &[Term]) -> Result<T, ConsumeErr>>,
}

impl<T> Clone for Fun<T> {
    fn clone(&self) -> Self {
        Self {
            tau: self.tau.clone(),
            fun: self.fun.clone(),
            span: self.span,
        }
    }
}

impl<T> PartialEq for Fun<T> {
    fn eq(&self, _other: &Self) -> bool {
        panic!()
    }
}

impl<T> Eq for Fun<T> {}

impl<T> Debug for Fun<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("MyFun").finish()
    }
}

pub struct Solved<T> {
    terms: Vec<Term>,
    inner: T,
}

impl<T> Deref for Solved<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Clone)]
pub struct Spanned<T: ?Sized> {
    pub span: SourceSpan,
    pub val: T,
}

impl<T: ?Sized> Spanned<T> {
    pub fn as_ref(&self) -> &T {
        &self.val
    }
}

impl<V: Val> Lambda<V> {
    pub fn inst(&self, var: &[V]) -> Spanned<Expr<V>> {
        (self.func)(var)
    }
}

#[allow(clippy::type_complexity)]
pub struct Lambda<V: Val, F = dyn Fn(&[V]) -> Spanned<Expr<V>>>
where
    F: ?Sized + Fn(&[V]) -> Spanned<Expr<V>>,
{
    pub _val: PhantomData<V>,
    pub func: F,
}

#[derive(Clone)]
pub struct Value<V> {
    pub inj: Vec<Free<V>>,
    pub span: Option<SourceSpan>,
}

impl<V> Default for Value<V> {
    fn default() -> Self {
        Self {
            inj: Default::default(),
            span: None,
        }
    }
}

pub struct FuncName<V: Val> {
    func: Weak<Lambda<V>>,
    typ: Fun<NegTyp>,
}

pub enum Thunk<V: Val> {
    Local(V::Func),
    Builtin(Builtin),
}

/// Named resource name
#[derive(Clone)]
pub struct Name {
    pub id: usize,
    pub typ: Fun<PosTyp>,
}

pub trait Val: Clone + Sized + 'static {
    type Func: Clone;
    fn make(
        desugar: &Desugar<Self>,
        lamb: &Weak<Lambda<Self>>,
        typ: &parse::types::NegTyp,
    ) -> Self::Func;
}

impl<T> From<&Spanned<T>> for SourceSpan {
    fn from(value: &Spanned<T>) -> Self {
        value.span
    }
}

impl<T> From<Fun<T>> for Option<SourceSpan> {
    fn from(value: Fun<T>) -> Self {
        value.span
    }
}

#[derive(Debug)]
pub struct InnerDiagnostic(Box<dyn Diagnostic + Send + Sync>);
impl InnerDiagnostic {
    pub fn new(err: impl Diagnostic + Send + Sync + 'static) -> Self {
        Self(Box::new(err))
    }
}

impl InnerDiagnostic {
    pub fn iter(&self) -> impl Iterator<Item = &dyn Diagnostic> {
        Some(&*self.0 as _).into_iter()
    }
}

pub enum Expr<V: Val> {
    /// construct a value and return it
    Return(Value<V>),

    /// apply a function to some arguments and bind the result in the continuation
    App(Thunk<V>, Value<V>, Rc<Lambda<V>>),

    /// define a different continuation,
    Cont(Rc<Lambda<V>>, V::Func, Box<Spanned<Expr<V>>>),

    /// match on some inductive type and choose a branch
    /// last branch will be the catch all
    Match(Free<V>, Vec<Spanned<Expr<V>>>),

    /// loop back to an assigment
    Loop(V::Func, Value<V>),

    Debug(Box<Spanned<Expr<V>>>),
}

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors do not destruct tuples
// - Remove EqualTerms
// - Use deep embedding for qualified types
// - Flatten types
// - No longer return constraints, verified eagerly now
// - Add support for mutable memory using resources
// - model functions as pointers
