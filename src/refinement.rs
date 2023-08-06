#![allow(dead_code)]

use std::{fmt::Debug, ops::Deref, rc::Rc};

mod constraint;
mod determined;
mod subst;
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
#[derive(PartialEq, Eq, Debug)]
enum Term {
    LVar(usize),
    UVar(usize, Sort),
    EVar(usize, Sort),
    Prop(Rc<Prop>),
    Zero,
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

#[derive(PartialEq, Eq, Debug)]
enum PosTyp {
    Prod(Vec<Rc<PosTyp>>),
    Refined(Rc<PosTyp>, Rc<Prop>),
    Exists(Sort, Rc<PosTyp>),
    Thunk(Rc<NegTyp>),
    Measured(Vec<(Rc<ProdFunctor>, Rc<Term>)>, Rc<Term>),
}

#[derive(PartialEq, Eq, Debug)]
enum NegTyp {
    Force(Rc<PosTyp>),
    Implies(Rc<Prop>, Rc<NegTyp>),
    Forall(Sort, Rc<NegTyp>),
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
