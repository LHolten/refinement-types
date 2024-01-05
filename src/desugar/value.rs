use crate::parse::expr::{BinOp, BinOpValue, Index, Spanned, Value};
use crate::parse::types::{Prop, PropOp};
use crate::{refinement, Nested};
use std::collections::HashMap;
use std::rc::Rc;

use super::ScopeErr;

impl Value {
    // convert a value to individual fields
    pub fn convert<T: Clone>(
        &self,
        lookup: &HashMap<String, Nested<T>>,
    ) -> Result<refinement::Free<T>, ScopeErr> {
        let res = match self {
            Value::Var(name, rest) => {
                let mut curr = lookup.try_get(name)?;
                let mut inner;
                for r in rest {
                    inner = curr.unwrap_more();
                    let Index::Attribute(attr) = r else { panic!() };
                    curr = inner.map.try_get(attr)?;
                }
                refinement::Free::Var(curr.unwrap_just().clone())
            }
            Value::Int32(val) => refinement::Free::Just(*val as i64, 32),
            Value::BinOp(binop) => binop.convert(lookup)?,
            Value::Prop(prop) => prop.convert(lookup)?,
        };
        Ok(res)
    }
}

impl BinOpValue {
    pub fn convert<T: Clone>(
        &self,
        lookup: &HashMap<String, Nested<T>>,
    ) -> Result<refinement::Free<T>, ScopeErr> {
        let op = match self.op {
            BinOp::Plus => refinement::BinOp::Add,
            BinOp::Minus => refinement::BinOp::Sub,
            BinOp::Times => refinement::BinOp::Mul,
            BinOp::Modulo => refinement::BinOp::Rem,
            BinOp::Divide => refinement::BinOp::Div,
            BinOp::Shl => refinement::BinOp::Shl,
            BinOp::Shr => refinement::BinOp::Shr,
        };
        Ok(refinement::Free::BinOp {
            l: Rc::new(self.l.convert(lookup)?),
            r: Rc::new(self.r.convert(lookup)?),
            op,
        })
    }
}

impl refinement::BinOp {
    pub fn free<T>(self, l: refinement::Free<T>, r: refinement::Free<T>) -> refinement::Free<T> {
        refinement::Free::BinOp {
            l: Rc::new(l),
            r: Rc::new(r),
            op: self,
        }
    }
}

impl Prop {
    pub fn convert<T: Clone>(
        &self,
        lookup: &HashMap<String, Nested<T>>,
    ) -> Result<refinement::Free<T>, ScopeErr> {
        let l = self.l.convert(lookup)?;
        let r = self.r.convert(lookup)?;
        use refinement::BinOp as Op;
        let res = match self.op {
            PropOp::Less => Op::Less.free(l, r),
            PropOp::LessEq => Op::LessEq.free(l, r),
            PropOp::Eq => Op::Eq.free(l, r),
            PropOp::NotEq => Op::NotEq.free(l, r),
            PropOp::And => Op::And.free(l, r),
            PropOp::Or => Op::Or.free(l, r),
            PropOp::MulSafe => Op::MulSafe.free(l, r),
            PropOp::AddSafe => Op::AddSafe.free(l, r),
        };
        Ok(res)
    }
}

pub trait IntoScope {
    type Item;
    fn try_get(&self, name: &Spanned<String>) -> Result<&Self::Item, ScopeErr>;
}

impl<V> IntoScope for HashMap<String, V> {
    type Item = V;

    fn try_get(&self, name: &Spanned<String>) -> Result<&Self::Item, ScopeErr> {
        self.get(&name.val).ok_or(ScopeErr { span: name.span })
    }
}
