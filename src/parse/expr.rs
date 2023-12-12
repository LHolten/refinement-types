use std::rc::Rc;

use miette::SourceSpan;

use super::types::{NamedConstraint, NegTyp, Prop};

pub enum Def {
    Func(FuncDef),
    Typ(NamedConstraint),
}

pub struct Spanned<T> {
    pub span: (usize, usize),
    pub val: T,
}

impl<T> Spanned<T> {
    pub fn source_span(&self) -> SourceSpan {
        (self.span.0, self.span.1 - self.span.0).into()
    }
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
    pub func: Option<String>,
    pub args: Spanned<Vec<Value>>,
}

pub enum Value {
    Var(String, Vec<String>),
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
}

pub enum Stmt {
    Let(Let),
    FuncDef(FuncDef),
    If(If),
    Unpack(Bind),
    Pack(Bind),
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
