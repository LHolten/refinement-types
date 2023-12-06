use crate::parse::expr::{BinOp, BinOpValue, Value};
use crate::parse::types::{Prop, PropOp};
use crate::refinement;
use std::collections::HashMap;
use std::rc::Rc;

impl Value {
    pub fn convert<T: Clone>(&self, lookup: &HashMap<String, T>) -> refinement::Free<T> {
        match self {
            Value::Var(name) => refinement::Free::Var(
                lookup
                    .get(name)
                    .ok_or_else(|| {
                        format!(
                            "can not find `{name}`, have: {:?}",
                            lookup.keys().collect::<Vec<_>>()
                        )
                    })
                    .unwrap()
                    .clone(),
            ),
            Value::Int32(val) => refinement::Free::Just(*val as i64, 32),
            Value::BinOp(binop) => binop.convert(lookup),
            Value::Prop(prop) => prop.convert(lookup),
        }
    }
}

impl BinOpValue {
    pub fn convert<T: Clone>(&self, lookup: &HashMap<String, T>) -> refinement::Free<T> {
        let op = match self.op {
            BinOp::Plus => refinement::BinOp::Add,
            BinOp::Minus => refinement::BinOp::Sub,
            BinOp::Times => refinement::BinOp::Mul,
            BinOp::Modulo => refinement::BinOp::Rem,
            BinOp::Divide => refinement::BinOp::Div,
        };
        refinement::Free::BinOp {
            l: Rc::new(self.l.convert(lookup)),
            r: Rc::new(self.r.convert(lookup)),
            op,
        }
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
    pub fn convert<T: Clone>(&self, lookup: &HashMap<String, T>) -> refinement::Free<T> {
        let l = self.l.convert(lookup);
        let r = self.r.convert(lookup);
        use refinement::BinOp as Op;
        match self.op {
            PropOp::Less => Op::Less.free(l, r),
            PropOp::LessEq => Op::LessEq.free(l, r),
            PropOp::Eq => Op::Eq.free(l, r),
            PropOp::NotEq => Op::NotEq.free(l, r),
            PropOp::And => Op::And.free(l, r),
            PropOp::MulSafe => Op::MulSafe.free(l, r),
        }
    }
}
