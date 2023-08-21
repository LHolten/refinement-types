#![allow(dead_code)]

use std::{cell::Cell, fmt::Debug, ops::Deref, rc::Rc};

mod constraint;
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

#[derive(Default)]
enum Constraint {
    #[default]
    True,
    And(Rc<Constraint>, Rc<Constraint>),
    Prop(Rc<Prop>),
    Context(ContextPart, Rc<Constraint>),
    SubNegTyp(Rc<NegTyp>, Rc<NegTyp>),
    SubPosTyp(Rc<PosTyp>, Rc<PosTyp>),
    Check(Rc<Expr>, Rc<NegTyp>),
}

// This is a constraint with additional substitutions
#[derive(Default)]
struct ExtendedConstraint {
    w: Rc<Constraint>,
    r: Vec<Option<Rc<Term>>>,
}

#[derive(PartialEq, Eq, Debug)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>),
}

#[allow(clippy::type_complexity)]
struct Fun<T> {
    tau: Sort,
    fun: Rc<dyn Fn(&Rc<Term>) -> Rc<T>>,
}

impl<T: PartialEq> PartialEq for Fun<T> {
    fn eq(&self, _other: &Self) -> bool {
        panic!("please dont compare qualified terms")
    }
}

impl<T: Eq> Eq for Fun<T> {}

impl<T: Debug> Debug for Fun<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Fun{{...}}")
    }
}

#[derive(PartialEq, Eq, Debug)]
enum PosTyp {
    Prod(Vec<Rc<PosTyp>>),
    Refined(Rc<PosTyp>, Rc<Prop>),
    Exists(Fun<PosTyp>),
    Thunk(Rc<NegTyp>),
    Measured(Vec<(Rc<ProdFunctor>, Rc<Term>)>, Rc<Term>),
}

#[derive(PartialEq, Eq, Debug)]
enum NegTyp {
    Force(Rc<PosTyp>),
    Implies(Rc<Prop>, Rc<NegTyp>),
    Forall(Fun<NegTyp>),
    Fun(Rc<PosTyp>, Rc<NegTyp>),
}

#[derive(PartialEq, Eq, Debug)]
struct ProdFunctor {
    prod: Vec<BaseFunctor>,
}

#[derive(PartialEq, Eq, Debug)]
enum BaseFunctor {
    Pos(Rc<PosTyp>),
    Id,
}

enum Value {
    // second argument is projections
    Var(usize, Vec<usize>),
    Inj(usize, Rc<Value>),
    Tuple(Vec<Rc<Value>>),
    Thunk(Rc<Expr>),
}

enum Expr {
    Return(Rc<Value>),
    Let(Rc<BoundExpr>, Rc<Expr>),
    Match(Rc<Head>, Vec<Expr>),
    Lambda(Rc<Expr>),
}

enum Head {
    // second argument is projections
    Var(usize, Vec<usize>),
    Anno(Rc<Value>, Rc<PosTyp>),
}

enum BoundExpr {
    App(Rc<Head>, Vec<Value>),
    Anno(Rc<Expr>, Rc<PosTyp>),
}

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors do not destruct tuples
// - Remove EqualTerms
// -
