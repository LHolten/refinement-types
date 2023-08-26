#![allow(dead_code)]

use std::{cell::Cell, fmt::Debug, ops::Deref, rc::Rc};

#[macro_use]
mod parse;
#[macro_use]
mod parse_expr;

mod eval;
mod subtyp;
#[cfg(test)]
mod test;
mod typing;
mod unroll;
mod verify;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Nat,
}

#[non_exhaustive]
#[derive(PartialEq, Eq, Debug, Clone)]
enum InnerTerm {
    UVar(usize, Sort),
    EVar(usize, Sort),
    Prop(Rc<Prop>),
    Zero,
}

#[repr(transparent)]
struct Term {
    value: Cell<Option<InnerTerm>>,
}

struct TermRef<'a> {
    term: &'a Cell<Option<InnerTerm>>,
    inner: Option<InnerTerm>,
}

impl Deref for TermRef<'_> {
    type Target = InnerTerm;

    fn deref(&self) -> &Self::Target {
        self.inner.as_ref().unwrap()
    }
}

impl Drop for TermRef<'_> {
    fn drop(&mut self) {
        let old = self.term.replace(self.inner.take());
        assert_eq!(old, None);
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        *self.borrow() == *other.borrow()
    }
}

impl Eq for Term {}

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.borrow().fmt(f)
    }
}

impl InnerTerm {
    fn share(self) -> Rc<Term> {
        Rc::new(Term {
            value: Cell::new(Some(self)),
        })
    }
}

impl Term {
    fn borrow(&self) -> TermRef {
        TermRef {
            term: &self.value,
            inner: self.value.take(),
        }
    }

    fn instantiate(&self, rhs: &Self) {
        let val = rhs.borrow().inner.clone();
        assert!(val.is_some());
        let old = self.value.replace(val);
        // TODO: if this is not empty, we could make a Prop
        assert!(matches!(old, Some(InnerTerm::EVar(_, _))));
    }
}

#[derive(Default)]
enum Context {
    #[default]
    Empty,
    Assume {
        phi: Prop,
        next: Rc<Context>,
    },
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut res = Vec::new();
        let mut this = self;
        while let Self::Assume { phi, next } = this {
            this = next;
            res.push(phi);
        }
        f.debug_list().entries(res.iter().rev()).finish()
    }
}

#[derive(Clone, Default)]
struct SubContext {
    exis: usize,
    univ: usize,
    assume: Rc<Context>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>),
}

// PosType is product like, it can contain any number of items
#[derive(PartialEq, Eq, Debug, Default, Clone)]
struct PosTyp {
    thunks: Vec<Fun<NegTyp>>,
    prop: Vec<Prop>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct Measured {
    // how to calculate the result term from each branch terms
    f_alpha: Vec<Fun<(PosTyp, Rc<Term>)>>,
}

#[derive(PartialEq, Eq, Debug)]
struct NegTyp {
    arg: PosTyp,
    ret: Fun<PosTyp>,
}

trait ListProp {
    fn props(&self) -> &[Prop];
}

impl ListProp for PosTyp {
    fn props(&self) -> &[Prop] {
        &self.prop
    }
}

impl ListProp for NegTyp {
    fn props(&self) -> &[Prop] {
        self.arg.props()
    }
}

impl ListProp for (PosTyp, Rc<Term>) {
    fn props(&self) -> &[Prop] {
        self.0.props()
    }
}

#[allow(clippy::type_complexity)]
struct Fun<T> {
    measured: Vec<Measured>,
    tau: Vec<Sort>,
    fun: Rc<dyn Fn(&[Rc<Term>]) -> T>,
}

impl<T> Clone for Fun<T> {
    fn clone(&self) -> Self {
        Self {
            tau: self.tau.clone(),
            fun: self.fun.clone(),
            measured: self.measured.clone(),
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
    args: Vec<Rc<Term>>,
    inner: T,
}

impl<T> Deref for Solved<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Clone)]
struct Var {
    args: Vec<(Rc<Term>, Measured)>,
    inner: Rc<PosTyp>,
}

impl Var {
    pub fn infer_inj(&self, proj: &usize) -> &(Rc<Term>, Measured) {
        &self.args[*proj]
    }

    // pub fn infer_inj(&self, proj: &usize) -> &Measured {
    //     &self.measured[*proj]
    // }

    pub fn infer_thunk(&self, proj: &usize) -> &Fun<NegTyp> {
        &self.inner.thunks[*proj]
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
    thunk: Vec<Thunk<V>>,
    inj: Vec<Inj<V>>,
}

impl<V> Default for Value<V> {
    fn default() -> Self {
        Self {
            thunk: Default::default(),
            inj: Default::default(),
        }
    }
}

enum Inj<V> {
    Just(usize, Rc<Value<V>>),
    // second argument is projection
    Var(V, usize),
}

enum Thunk<V> {
    Just(Lambda<V>),
    Var(V, usize),
}

enum Expr<V> {
    // construct a value and return it
    Return(Rc<Value<V>>),

    // execute an expression and bind the result in the continuation
    Let(BoundExpr<V>, Lambda<V>),

    // match on some inductive type and choose a branch
    Match(V, usize, Vec<Lambda<V>>),

    // tail call, can be used for loops
    Tail(V, usize, Rc<Value<V>>),
}

enum BoundExpr<V> {
    // apply a function to some arguments
    App(V, usize, Rc<Value<V>>),

    // define a set of (mutually recursive) functions
    Anno(Lambda<V>, Vec<Fun<NegTyp>>),
}

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors do not destruct tuples
// - Remove EqualTerms
// - Use deep embedding for qualified types
// - Flatten types
// - No longer return constraints, verified eagerly now
