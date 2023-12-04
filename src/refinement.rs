#![allow(dead_code)]

use std::marker::PhantomData;
use std::rc::{Rc, Weak};
use std::{fmt::Debug, ops::Deref};

#[macro_use]
mod parse_typ;

pub mod builtin;
pub mod eval;
pub mod heap;
mod subtyp;
#[cfg(test)]
mod test;
pub mod typing;
mod unroll;
mod verify;

use miette::{Diagnostic, SourceSpan};
use z3::ast::{Ast, Bool, Dynamic, BV};
use z3::Sort;

use crate::parse;
use crate::parse::desugar::Desugar;
use crate::solver::ctx;

use self::heap::{ConsumeErr, FuncTerm, Heap};

use self::builtin::Builtin;

#[derive(Clone)]
pub enum Term {
    BV(BV<'static>),
    Bool(Bool<'static>),
}

/// Uninterpreted term
#[derive(Clone)]
pub struct UnTerm {
    inner: Dynamic<'static>,
}

impl UnTerm {
    // pub fn new(val: &dyn Ast) -> Self {
    //     Self {
    //         inner: Dynamic::from_ast(val),
    //     }
    // }

    pub fn byte(&self) -> Term {
        todo!()
    }
}

impl UnTerm {
    pub fn eq(&self, other: &Self) -> Term {
        Term::Bool(self.inner._eq(&other.inner))
    }
}

impl UnTerm {
    pub fn fresh() -> Self {
        let sort = Sort::uninterpreted(ctx(), "World".into());
        Self {
            inner: Dynamic::fresh_const(ctx(), "world", &sort),
        }
    }
}

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::BV(bv) => bv.fmt(f),
            Term::Bool(b) => b.fmt(f),
        }
    }
}

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
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct Cond {
    pub named: Weak<Name>,
    // only if the cond is `true`, does this named resource exist
    pub cond: Term,
    // these are the arguments to the named resource
    pub args: Vec<Term>,
    pub span: SourceSpan,
}

/// a single resource
#[derive(Clone)]
pub enum Resource {
    Named(Weak<Name>),
    Owned,
}

#[derive(Clone)]
pub struct Forall {
    pub named: Resource,
    // mask specifies where is valid
    pub mask: FuncTerm,
    pub span: Option<SourceSpan>,
}

#[derive(Clone)]
pub struct ForallTerm {
    pub forall: Forall,
    pub func: FuncTerm,
}

#[derive(Clone, Default)]
#[must_use]
pub struct SubContext {
    assume: Vec<Term>,
    forall: Vec<ForallTerm>,
    // funcs: Vec<FuncName>,
}

#[derive(Clone, Default)]
pub struct PosTyp;

#[derive(Clone)]
pub struct NegTyp {
    pub arg: PosTyp,
    pub ret: Fun<PosTyp>,
}

#[allow(clippy::type_complexity)]
pub struct Fun<T, A = ()> {
    // the arguments that are expected to be in scope
    pub tau: Vec<(u32, String)>,
    pub span: Option<SourceSpan>,
    pub fun: Rc<dyn Fn(&mut dyn Heap, &[Term], A) -> Result<T, ConsumeErr>>,
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

// #[derive(Clone)]
// pub enum Data {
//     Func(FuncTerm),
//     UnTerm(UnTerm),
//     Named(Vec<Data>),
// }

// impl Data {
//     pub fn as_func(&mut self, name: Resource) -> FuncTerm {
//         match self {
//             Data::Func(func) => func.clone(),
//             Data::UnTerm(unterm) => todo!(),
//             Data::Named(_) => panic!(),
//         }
//     }

//     pub fn as_named(&mut self) -> Data {
//         match self {
//             Data::Func(_) => panic!(),
//             Data::UnTerm(inner) => Data::UnTerm(inner.clone()),
//             Data::Named(list) => list.remove(0),
//         }
//     }
// }

/// Named resource name
pub struct Name {
    pub id: usize,
    pub func: Rc<dyn Fn(&mut dyn Heap, &mut dyn Dir, &[Term]) -> Result<(), ConsumeErr>>,
    // pub free: Fun<Data>,
    // pub exact: Fun<PosTyp, Data>,
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
        Spanned {
            span: self.span,
            val: (self.func)(var),
        }
    }
}

#[allow(clippy::type_complexity)]
pub struct Lambda<V: Val, F = dyn Fn(&[V]) -> Expr<V>>
where
    F: ?Sized + Fn(&[V]) -> Expr<V>,
{
    pub _val: PhantomData<V>,
    pub span: SourceSpan,
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

impl<V: Val> From<&Lambda<V>> for SourceSpan {
    fn from(value: &Lambda<V>) -> Self {
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

    /// execute an expression and bind the result in the continuation
    Let(BoundExpr<V>, Rc<Lambda<V>>),

    /// match on some inductive type and choose a branch
    /// last branch will be the catch all
    Match(Free<V>, Vec<Rc<Lambda<V>>>),

    /// loop back to an assigment
    Loop(V::Func, Value<V>),
}

pub enum BoundExpr<V: Val> {
    /// apply a function to some arguments
    App(Thunk<V>, Value<V>),

    /// define a different continuation,
    Cont(Rc<Lambda<V>>, V::Func),
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
