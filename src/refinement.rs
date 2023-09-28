#![allow(dead_code)]

use std::process::abort;
use std::rc::Rc;
use std::{fmt::Debug, ops::Deref};

#[macro_use]
mod parse_typ;
#[macro_use]
mod parse_expr;

mod builtin;
mod eval;
mod heap;
mod subtyp;
#[cfg(test)]
mod test;
mod typing;
mod unroll;
mod util;
mod verify;

pub use typing::Var;

use self::heap::{Heap, Resource};

use self::builtin::Builtin;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Nat,
}

#[non_exhaustive]
#[derive(PartialEq, Eq, Clone)]
enum Term {
    UVar(u32, Sort),
    Nat(usize),
    Add(Rc<Term>, Rc<Term>),
    Bool(Rc<Prop>),
}

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UVar(idx, _tau) => write!(f, "var{idx}"),
            Self::Nat(val) => write!(f, "{val}"),
            Self::Add(l, r) => write!(f, "{l:?} + {r:?}"),
            Self::Bool(val) => write!(f, "{val:?}"),
        }
    }
}

#[derive(PartialEq, Eq, Clone)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>),
    LessEq(Rc<Term>, Rc<Term>),
    // MeasureEq(Measure, [Rc<Term>; 2]),
    // True,
}

impl Debug for Prop {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Eq(l, r) => write!(f, "{l:?} == {r:?}"),
            Self::LessEq(l, r) => write!(f, "{l:?} <= {r:?}"),
        }
    }
}

#[allow(clippy::type_complexity)]
#[derive(Clone, Debug)]
struct Cond {
    args: Vec<Rc<Term>>,
    func: fn(&mut dyn Heap, u32, &[Rc<Term>]),
}

#[derive(Clone)]
struct FuncDef {
    ptr: Rc<Term>,
    typ: Fun<NegTyp>,
}

#[derive(Clone, Default)]
#[must_use]
struct SubContext {
    univ: u32,
    assume: Vec<Prop>,
    alloc: Vec<Resource>,
    cond: Vec<Cond>,
    funcs: Vec<FuncDef>,
}

impl Drop for SubContext {
    fn drop(&mut self) {
        abort()
    }
}

#[derive(PartialEq, Eq, Debug, Default, Clone)]
struct PosTyp;

#[derive(PartialEq, Eq, Debug)]
struct NegTyp {
    arg: PosTyp,
    ret: Fun<PosTyp>,
}

#[derive(Debug, Clone)]
struct ResSort {
    tau: Sort,
    ptr: Rc<Term>,
}

#[allow(clippy::type_complexity)]
struct Fun<T> {
    // the arguments that are expected to be in scope
    tau: Vec<Sort>,
    fun: Rc<dyn Fn(&[Rc<Term>], &mut dyn Heap) -> T>,
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
    terms: Vec<Rc<Term>>,
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
struct Lambda<V>(Rc<dyn Fn(&V) -> Expr<V>>);

impl<V> Clone for Lambda<V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

struct Value<V> {
    inj: Vec<Inj<V>>,
}

impl<V> Default for Value<V> {
    fn default() -> Self {
        Self {
            inj: Default::default(),
        }
    }
}

enum Inj<V> {
    Just(usize),
    Var(Local<V>),
}

enum Thunk<V> {
    Local(Local<V>),
    Builtin(Builtin),
}

struct Local<V>(V, usize);

enum Expr<V> {
    /// construct a value and return it
    Return(Rc<Value<V>>),

    /// execute an expression and bind the result in the continuation
    Let(BoundExpr<V>, Lambda<V>),

    /// match on some inductive type and choose a branch
    /// last branch will be the catch all
    Match(Local<V>, Vec<Lambda<V>>),

    /// loop back to an assigment
    Loop(V, Rc<Value<V>>),
}

enum BoundExpr<V> {
    /// apply a function to some arguments
    App(Thunk<V>, Rc<Value<V>>),

    Anno(Rc<Value<V>>, Fun<PosTyp>),
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
