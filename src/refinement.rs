#![allow(unused)]

use std::{cell::Cell, rc::Rc};

mod subtyp;
mod typing;
mod verify;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Sort;

#[derive(PartialEq, Eq)]
enum Term {
    Var(usize),
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
    // I added this one to do lazy substitution
    Exists(Sort, Rc<Term>, Rc<Constraint>),
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
    Prod(Rc<PosTyp>, Rc<PosTyp>),
    Sum(Rc<PosTyp>, Rc<PosTyp>),
    Refined(Rc<PosTyp>, Rc<Prop>),
    Exists(Sort, Rc<PosTyp>),
    Thunk(Rc<NegTyp>),
    Measured(Rc<SumFunctor>, Algebra, Rc<Term>),
}

#[derive(PartialEq, Eq)]
enum NegTyp {
    Force(Rc<PosTyp>),
    Implies(Rc<Prop>, Rc<NegTyp>),
    Forall(Sort, Rc<NegTyp>),
    Fun(Rc<PosTyp>, Rc<NegTyp>),
}

#[derive(PartialEq, Eq)]
struct SumFunctor {
    sum: Vec<ProdFunctor>,
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

#[derive(PartialEq, Eq)]
struct SumPattern {
    idx: usize,
    pat: Rc<ProdPattern>,
}

#[derive(PartialEq, Eq)]
struct ProdPattern {
    parts: Vec<BasePattern>,
}

#[derive(PartialEq, Eq)]
enum BasePattern {
    Ignore,
    Var,
    Pack,
}

#[derive(PartialEq, Eq)]
struct Algebra {
    pats: Vec<(SumPattern, Term)>,
}

struct Pattern;

enum Value {
    Var(usize),
    Pair(Rc<Value>, Rc<Value>),
    Thunk(Rc<Expr>),
}

enum Expr {
    Return(Rc<Value>),
    Let(Rc<BoundExpr>, Rc<Expr>),
    Match(Rc<Head>, Vec<(Pattern, Expr)>),
    Lambda(Rc<Expr>),
}

enum Head {
    Var(usize),
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
