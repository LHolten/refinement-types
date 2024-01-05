use std::rc::Rc;

use miette::SourceSpan;

use super::types::{NamedConstraint, NegTyp, Prop};

pub enum Def {
    Func(FuncDef),
    Typ(NamedConstraint),
}

pub struct Spanned<T> {
    pub span: SourceSpan,
    pub val: T,
}

pub struct Module(pub Vec<Def>);

pub struct FuncDef {
    pub name: String,
    pub typ: NegTyp,
    pub block: Rc<Spanned<Block>>,
}

pub struct Let {
    pub names: Vec<String>,
    pub bind: Bind,
}

pub struct Bind {
    pub func: Option<Spanned<String>>,
    pub args: Spanned<Vec<Value>>,
}

pub enum Index {
    Attribute(Spanned<String>),
    Value(Value),
}

pub enum Value {
    Var(Spanned<String>, Vec<Index>),
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
    Modulo,
    Divide,
    Shl,
    Shr,
}

pub enum Stmt {
    Let(Let),
    Debug,
    FuncDef(FuncDef),
    If(If),
}

pub enum Block {
    Stmt {
        step: Spanned<Stmt>,
        next: Rc<Spanned<Block>>,
    },
    End(Bind),
}

pub struct IfZero {
    pub val: Value,
    pub block: Rc<Spanned<Block>>,
}

pub struct If {
    pub val: Value,
    pub block: Rc<Spanned<Block>>,
}
