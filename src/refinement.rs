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
use z3::ast::BV;

use self::heap::{BoolFuncTerm, Heap};

use self::builtin::Builtin;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Nat,
}

#[derive(PartialEq, Eq, Clone)]
struct Term(BV<'static>);

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[allow(clippy::type_complexity)]
#[derive(Clone, Debug)]
struct Cond {
    // only if the cond is `true`, does this named resource exist
    cond: Term,
    // these are the arguments to the named resource
    args: Vec<Term>,
    func: fn(&mut dyn Heap, &[Term]),
}

#[derive(Clone)]
struct Forall {
    // all args are universally quantified
    func: fn(&mut dyn Heap, &[Term]),
    // mask specifies where is valid
    mask: Rc<BoolFuncTerm>,
    arg_size: Vec<u32>,
}

#[derive(Clone)]
struct FuncDef {
    ptr: Term,
    typ: Fun<NegTyp>,
}

/// a single resource
#[derive(Clone)]
struct Resource {
    pub ptr: Term,
    pub value: Term,
}

#[derive(Clone, Default)]
#[must_use]
struct SubContext {
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
struct PosTyp;

#[derive(PartialEq, Eq, Debug)]
struct NegTyp {
    arg: PosTyp,
    ret: Fun<PosTyp>,
}

impl NegTyp {
    pub fn new(ret: Fun<PosTyp>) -> Self {
        NegTyp { arg: PosTyp, ret }
    }
}

#[allow(clippy::type_complexity)]
struct Fun<T> {
    // the arguments that are expected to be in scope
    tau: Vec<u32>,
    // the first argument is the function itself
    fun: Rc<dyn Fn(&[Term], &mut dyn Heap) -> T>,
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
    Just(i64, u32),
    Var(Local<V>),
}

enum Thunk<V> {
    Local(Local<V>),
    Builtin(Builtin),
}

#[derive(Clone)]
struct Local<V>(V, usize);

/// Named resource name
struct Name {
    tau: Vec<u32>,
    func: fn(&mut dyn Heap, &[Term]),
}

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
