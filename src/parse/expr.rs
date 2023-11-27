use std::rc::Rc;

use super::types::{NamedConstraint, NegTyp, Prop};

pub enum Def {
    Func(FuncDef),
    Typ(NamedConstraint),
}

pub struct Module(pub Vec<Def>);

pub struct FuncDef {
    pub name: String,
    pub typ: NegTyp,
    pub block: Rc<Block>,
}

pub struct Let {
    pub names: Vec<String>,
    pub bind: Bind,
}

pub struct Bind {
    pub func: Option<String>,
    pub args: Vec<Value>,
}

pub enum Value {
    Var(String),
    Int32(i32),
    BinOp(Box<BinOpValue>),
    Prop(Box<Prop>),
}

pub struct BinOpValue {
    pub l: Value,
    pub r: Value,
    pub op: BinOp,
}

pub enum BinOp {
    Plus,
    Minus,
    Times,
}

pub enum Stmt {
    Let(Let),
    FuncDef(FuncDef),
    IfZero(IfZero),
    Unpack(Bind),
    Pack(Bind),
}

pub struct Block {
    pub steps: Vec<Stmt>,
    pub end: Bind,
}

pub struct IfZero {
    pub val: Value,
    pub block: Rc<Block>,
}
