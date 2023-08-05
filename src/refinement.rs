#![allow(dead_code)]

use std::{collections::VecDeque, fmt::Debug, ops::Deref, rc::Rc};

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
    GVar(usize),
    Prop(Rc<Prop>),
    Zero,
}

#[derive(Debug)]
enum ContextPart {
    Assume(Rc<Prop>),
    Free(Sort),
}

#[derive(Default)]
enum Context {
    #[default]
    Empty,
    Cons {
        part: ContextPart,
        next: Rc<Context>,
    },
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut res = Vec::new();
        let mut this = self;
        while let Self::Cons { part, next } = this {
            this = next;
            res.push(part);
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

#[derive(PartialEq, Eq, Debug)]
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
