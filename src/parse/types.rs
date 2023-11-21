//! this is for a separate type alias files

use std::rc::Rc;

use super::expr::{Bind, Value};

#[derive(Clone)]
pub struct NamedConstraint {
    pub name: String,
    pub typ: Rc<PosTyp>,
}

pub struct PosTyp {
    pub names: Vec<String>,
    pub parts: Vec<Constraint>,
}

#[derive(Clone)]
pub struct NegTyp {
    pub args: Rc<PosTyp>,
    pub ret: Rc<PosTyp>,
}

pub enum Constraint {
    Forall(Forall),
    Assert(Prop),
    // Func(Term, NegTyp),
    Builtin(String, Bind),
}

pub struct Forall {
    pub named: String,
    pub names: Vec<String>,
    pub cond: Rc<Prop>,
}

pub enum PropOp {
    Less,
    LessEq,
    Eq,
    NotEq,
    And,
}

pub struct Prop {
    pub l: Value,
    pub r: Value,
    pub op: PropOp,
}
