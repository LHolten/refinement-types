#![allow(dead_code)]

use std::{cell::Cell, fmt::Debug, ops::Deref, rc::Rc};

mod determined;
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

#[derive(Debug, Clone)]
enum ContextPart {
    Assume(Rc<Prop>),
    Free,
}

#[derive(Default)]
enum Context {
    #[default]
    Empty,
    Assume {
        phi: Rc<Prop>,
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

#[derive(Default)]
enum VarContext {
    #[default]
    Empty,
    Cons {
        typ: Rc<PosTyp>,
        next: Rc<VarContext>,
    },
}

#[derive(Clone, Default)]
struct SubContext {
    exis: usize,
    univ: usize,
    assume: Rc<Context>,
}

#[derive(Clone, Default)]
struct FullContext {
    sub: SubContext,
    var: Rc<VarContext>,
}

impl Deref for FullContext {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        &self.sub
    }
}

#[derive(PartialEq, Eq, Debug)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>),
}

// PosType is product like, it can contain any number of items
#[derive(PartialEq, Eq, Debug, Default)]
struct PosTyp {
    measured: Vec<Measured>,
    thunks: Vec<Fun<NegTyp>>,
}

#[derive(PartialEq, Eq, Debug)]
struct Measured {
    f_alpha: Vec<Fun<(PosTyp, Rc<Term>)>>,
    term: Rc<Term>,
}

#[derive(PartialEq, Eq, Debug)]
struct NegTyp {
    arg: PosTyp,
    ret: Fun<PosTyp>,
}

#[allow(clippy::type_complexity)]
struct Fun<T> {
    tau: Vec<Sort>,
    fun: Rc<dyn Fn(&[Rc<Term>]) -> (T, Vec<Rc<Prop>>)>,
}

impl<T> Clone for Fun<T> {
    fn clone(&self) -> Self {
        Self {
            tau: self.tau.clone(),
            fun: self.fun.clone(),
        }
    }
}

struct Unsolved<T> {
    args: Vec<Rc<Term>>,
    inner: T,
}

impl<T> Unsolved<T> {
    fn assert_resolved(&self) {
        let res = self
            .args
            .iter()
            .all(|arg| !matches!(*arg.borrow(), InnerTerm::EVar(_, _)));
        assert!(res)
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

#[derive(Default)]
struct Value {
    thunk: Vec<Thunk>,
    inj: Vec<Inj>,
}

enum Inj {
    Just(usize, Rc<Value>),
    // second argument is projection
    Var(usize, usize),
}

#[derive(Clone)]
enum Thunk {
    Just(Rc<Expr>),
    Var(usize, usize),
}

enum Expr {
    Return(Rc<Value>),
    Let(Rc<BoundExpr>, Rc<Expr>),
    Match(usize, usize, Vec<Expr>),
}

enum BoundExpr {
    App(usize, usize, Rc<Value>),
    // expression that does not take any arguments, we thus only store the return type
    Anno(Rc<Expr>, Fun<PosTyp>),
}

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors do not destruct tuples
// - Remove EqualTerms
// - Use deep embedding for qualified types
// - Flatten types
// - No longer return constraints, verified eagerly now
