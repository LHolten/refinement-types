#![allow(dead_code)]

use std::{cell::Cell, rc::Rc};

mod determined;
mod subtyp;
mod typing;
mod unroll;
mod verify;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Nat,
}

#[non_exhaustive]
#[derive(PartialEq, Eq)]
enum Term {
    Var(usize),
    Prop(Rc<Prop>),
}

enum ContextPart {
    Assume(Rc<Prop>),
    Free(Sort),
}

enum Context<'a> {
    Empty,
    Cons {
        sort: Sort,
        term: Cell<Option<Term>>,
        next: &'a Context<'a>,
    },
}

enum Constraint {
    True,
    And(Rc<Constraint>, Rc<Constraint>),
    Prop(Rc<Prop>),
    PropEq(Rc<Prop>, Rc<Prop>),
    Forall(Sort, Rc<Constraint>),
    Implies(Rc<Prop>, Rc<Constraint>),
    EqNegTyp(Rc<NegTyp>, Rc<NegTyp>),
    EqPosTyp(Rc<PosTyp>, Rc<PosTyp>),
    SubNegTyp(Rc<NegTyp>, Rc<NegTyp>),
    SubPosTyp(Rc<PosTyp>, Rc<PosTyp>),
}

#[derive(PartialEq, Eq)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>),
}

#[derive(PartialEq, Eq)]
enum PosTyp {
    Prod(Vec<Rc<PosTyp>>),
    Refined(Rc<PosTyp>, Rc<Prop>),
    Exists(Sort, Rc<PosTyp>),
    Thunk(Rc<NegTyp>),
    Measured(Vec<(Rc<ProdFunctor>, Rc<Term>)>, Rc<Term>),
}

#[derive(PartialEq, Eq)]
enum NegTyp {
    Force(Rc<PosTyp>),
    Implies(Rc<Prop>, Rc<NegTyp>),
    Forall(Sort, Rc<NegTyp>),
    Fun(Rc<PosTyp>, Rc<NegTyp>),
}

#[derive(PartialEq, Eq)]
struct ProdFunctor {
    prod: Vec<BaseFunctor>,
}

#[derive(PartialEq, Eq)]
enum BaseFunctor {
    Pos(Rc<PosTyp>),
    Id,
}

// #[derive(PartialEq, Eq)]
// struct SumPattern {
//     idx: usize,
//     pat: Rc<ProdPattern>,
// }

#[derive(PartialEq, Eq)]
struct ProdPattern {
    parts: Vec<BasePattern>,
}

#[derive(PartialEq, Eq)]
enum BasePattern {
    Ignore,
    Var(usize),
    Pack,
}

struct Pattern;

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

enum TConstraint {
    Cons(Rc<Constraint>),
    And(Rc<TConstraint>, Rc<TConstraint>),
    Check(Rc<Expr>, Rc<NegTyp>),
}

impl TConstraint {
    pub fn apply(&self, t: &Term) -> Self {
        todo!()
    }
}

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors should not deal with products?
//      maybe they just have Id in scope?
