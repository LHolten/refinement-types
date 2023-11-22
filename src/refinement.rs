#![allow(dead_code)]

use std::process::abort;
use std::rc::{Rc, Weak};
use std::sync::atomic::{AtomicUsize, Ordering};
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
mod util;
mod verify;

pub use typing::Var;
use z3::ast::{Bool, BV};

use self::heap::{BoolFuncTerm, Heap};

use self::builtin::Builtin;

#[derive(Clone)]
pub enum Term {
    BV(BV<'static>),
    Bool(Bool<'static>),
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
    Eq,
    Less,
    LessEq,
    NotEq,
    And,
}

#[allow(clippy::type_complexity)]
#[derive(Clone)]
pub struct Cond {
    pub named: Weak<Name>,
    // only if the cond is `true`, does this named resource exist
    pub cond: Term,
    // these are the arguments to the named resource
    pub args: Vec<Term>,
}

#[derive(Clone)]
pub struct Forall {
    pub named: Weak<Name>,
    // mask specifies where is valid
    pub mask: Rc<BoolFuncTerm>,
}

#[derive(Clone)]
pub struct FuncDef {
    ptr: Term,
    typ: Fun<NegTyp>,
}

/// a single resource
#[derive(Clone)]
pub struct Resource {
    pub ptr: Term,
    pub value: Term,
}

#[derive(Clone, Default)]
#[must_use]
pub struct SubContext {
    assume: Vec<Term>,
    alloc: Vec<Resource>,
    forall: Vec<Forall>,
    funcs: Vec<FuncDef>,
}

impl Drop for SubContext {
    fn drop(&mut self) {
        use std::backtrace::Backtrace;
        eprintln!(
            "dropped SubContext at location: {}",
            Backtrace::force_capture()
        );
        abort()
    }
}

#[derive(PartialEq, Eq, Debug, Default, Clone)]
pub struct PosTyp;

#[derive(PartialEq, Eq, Debug)]
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
    pub tau: Vec<u32>,
    pub fun: Rc<dyn Fn(&mut dyn Heap, &[Term]) -> T>,
}

impl<T> Clone for Fun<T> {
    fn clone(&self) -> Self {
        Self {
            tau: self.tau.clone(),
            fun: self.fun.clone(),
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

impl<V> Lambda<V> {
    pub fn inst(&self, var: &V) -> Expr<V> {
        (self.0)(var)
    }

    pub fn new<F: Fn(&V) -> Expr<V> + 'static>(fun: F) -> Self {
        Self(Rc::new(fun))
    }
}

#[allow(clippy::type_complexity)]
pub struct Lambda<V>(pub Rc<dyn Fn(&V) -> Expr<V>>);

impl<V> Clone for Lambda<V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

pub struct Value<V> {
    pub inj: Vec<Free<Local<V>>>,
}

impl<V> Default for Value<V> {
    fn default() -> Self {
        Self {
            inj: Default::default(),
        }
    }
}

pub enum Thunk<V> {
    Local(Local<V>),
    Builtin(Builtin),
}

#[derive(Clone)]
pub struct Local<V>(pub V, pub usize);

/// Named resource name
#[derive(Clone)]
pub struct Name {
    pub id: usize,
    pub typ: Fun<PosTyp>,
}

impl Name {
    pub fn new(typ: Fun<PosTyp>) -> Self {
        static NAME_ID: AtomicUsize = AtomicUsize::new(0);
        Self {
            id: NAME_ID.fetch_add(1, Ordering::Relaxed),
            typ,
        }
    }
}

pub enum Expr<V> {
    /// construct a value and return it
    Return(Rc<Value<V>>),

    /// execute an expression and bind the result in the continuation
    Let(BoundExpr<V>, Lambda<V>),

    /// match on some inductive type and choose a branch
    /// last branch will be the catch all
    Match(Free<Local<V>>, Vec<Lambda<V>>),

    /// loop back to an assigment
    Loop(V, Rc<Value<V>>),
}

pub enum BoundExpr<V> {
    /// apply a function to some arguments
    App(Thunk<V>, Rc<Value<V>>),

    /// define a different continuation,
    Cont(Lambda<V>, Fun<NegTyp>),
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
