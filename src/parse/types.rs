//! this is for a separate type alias files

use std::rc::Rc;

use super::expr::{Spanned, Value};

#[derive(Clone)]
pub struct NamedConstraint {
    pub name: String,
    pub typ: Rc<Spanned<PosTyp>>,
}

#[derive(Clone)]
pub enum ParamTyp {
    I32,
    Custom {
        name: String,
        // args: Vec<ParamTypArg>,
    },
}

// pub enum ParamTypArg {
//     Bind(Option<String>),
//     Exactly(Value),
// }

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
    Exactly(Spanned<String>),
}

pub struct Forall {
    pub named: Spanned<String>,
    pub names: Vec<String>,
    pub cond: Rc<Prop>,
}

pub struct Switch {
    pub cond: Option<Value>,
    pub named: Spanned<String>,
    pub args: Vec<Value>,
}

pub enum PropOp {
    Less,
    LessEq,
    Eq,
    NotEq,
    And,
    Or,
    MulSafe,
    AddSafe,
}

pub struct Prop {
    pub l: Value,
    pub r: Value,
    pub op: PropOp,
}
