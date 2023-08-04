#![allow(dead_code)]

use std::{cell::Cell, collections::VecDeque, default, ops::Deref, rc::Rc};

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
    LVar(usize),
    Prop(Rc<Prop>),
}

enum ContextPart {
    // existential is free + assume
    Existential(Sort, Cell<Option<Term>>),
    Assume(Rc<Prop>),
    Free(Sort),
}

enum Context {
    Empty,
    Cons {
        part: ContextPart,
        next: Rc<Context>,
    },
}

enum VarContext {
    Empty,
    Cons {
        typ: Rc<PosTyp>,
        next: Rc<VarContext>,
    },
}

struct FullContext {
    ctx: Rc<Context>,
    var: Rc<VarContext>,
}

impl Deref for FullContext {
    type Target = Context;

    fn deref(&self) -> &Self::Target {
        self.ctx.as_ref()
    }
}

#[derive(Default)]
enum Constraint {
    #[default]
    True,
    And(Rc<Constraint>, Rc<Constraint>),
    Prop(Rc<Prop>),
    PropEq(Rc<Prop>, Rc<Prop>),
    Forall(Sort, Rc<Constraint>),
    Implies(Rc<Prop>, Rc<Constraint>),
    SubNegTyp(Rc<NegTyp>, Rc<NegTyp>),
    SubPosTyp(Rc<PosTyp>, Rc<PosTyp>),
    Check(Rc<Expr>, Rc<NegTyp>),
}

// This is a constraint with additional substitutions
#[derive(Default)]
struct ExtendedConstraint {
    w: Rc<Constraint>,
    r: VecDeque<Option<Rc<Term>>>,
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

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors should not deal with products?
//      maybe they just have Id in scope?
