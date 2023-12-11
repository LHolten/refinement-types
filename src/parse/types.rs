//! this is for a separate type alias files

use std::rc::Rc;

use super::expr::{Bind, Spanned, Value};

#[derive(Clone)]
pub struct NamedConstraint {
    pub name: String,
    pub typ: Rc<Spanned<PosTyp>>,
}

pub struct PosTyp {
    pub names: Vec<String>,
    pub parts: Vec<Spanned<Constraint>>,
}

#[derive(Clone)]
pub struct NegTyp {
    pub args: Rc<Spanned<PosTyp>>,
    pub ret: Rc<Spanned<PosTyp>>,
}

pub enum Constraint {
    Forall(Forall),
    Switch(Option<String>, Switch),
    Assert(Prop),
    Let(String, Value),
    // Func(Term, NegTyp),
    Inline(Option<String>, Bind),
    Exactly(String),
}

pub struct Forall {
    pub named: String,
    pub names: Vec<String>,
    pub cond: Rc<Prop>,
}

pub struct Switch {
    pub cond: Option<Value>,
    pub named: String,
    pub args: Vec<Value>,
}

pub enum PropOp {
    Less,
    LessEq,
    Eq,
    NotEq,
    And,
    MulSafe,
}

pub struct Prop {
    pub l: Value,
    pub r: Value,
    pub op: PropOp,
}
