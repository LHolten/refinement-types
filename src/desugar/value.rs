use crate::parse::expr::{BinOp, BinOpValue, Value};
use crate::parse::types::{Prop, PropOp};
use crate::refinement::typing::zip_eq;
use crate::{refinement, Nested};
use std::collections::HashMap;
use std::rc::Rc;

pub enum ValTyp {
    I32,
    Named {
        id: Option<usize>,
        args: Vec<(String, ValTyp)>,
    },
}

impl<T: Clone> Nested<T> {
    pub fn collect(&self, typ: &ValTyp) -> Vec<refinement::Free<T>> {
        match typ {
            ValTyp::I32 => vec![refinement::Free::Var(self.clone().unwrap_just())],
            ValTyp::Named { id, args } => {
                let Self::More(id2, map) = self else { panic!() };
                assert_eq!(id, id2);
                args.iter()
                    .flat_map(|(name, typ)| map[name].collect(typ))
                    .collect()
            }
        }
    }
}

impl ValTyp {
    pub fn consume<T: Clone>(self, arg_iter: &mut impl Iterator<Item = T>) -> Nested<T> {
        match self {
            ValTyp::I32 => Nested::Just(arg_iter.next().unwrap()),
            ValTyp::Named { id, args } => Nested::More(
                id,
                args.into_iter()
                    .map(|(name, typ)| (name, typ.consume(arg_iter)))
                    .collect(),
                // TODO: add inner variables
            ),
        }
    }
}

impl Value {
    // convert a value to individual fields
    pub fn convert<T: Clone>(
        &self,
        lookup: &HashMap<String, Nested<T>>,
        typ: ValTyp,
    ) -> Vec<refinement::Free<T>> {
        match self {
            Value::Var(name, rest) => {
                let mut curr = lookup
                    .get(name)
                    .ok_or_else(|| {
                        format!(
                            "can not find `{name}`, have: {:?}",
                            lookup.keys().collect::<Vec<_>>()
                        )
                    })
                    .unwrap();
                for r in rest {
                    match curr {
                        Nested::More(_, lookup) => curr = lookup.get(r).unwrap(),
                        _ => panic!(),
                    }
                }
                curr.collect(&typ)
            }
            Value::Int32(val) => {
                let ValTyp::I32 = typ else { panic!() };
                vec![refinement::Free::Just(*val as i64, 32)]
            }
            Value::BinOp(binop) => vec![binop.convert(lookup, typ)],
            Value::Prop(prop) => vec![prop.convert(lookup, typ)],
            Value::Struct(_name, vals) => {
                // TODO: check that name == id?
                let ValTyp::Named { id: _, args } = typ else {
                    panic!()
                };
                zip_eq(args, vals)
                    .flat_map(|((_name, typ), val)| val.convert(lookup, typ))
                    .collect()
            }
        }
    }
}

impl BinOpValue {
    pub fn convert<T: Clone>(
        &self,
        lookup: &HashMap<String, Nested<T>>,
        typ: ValTyp,
    ) -> refinement::Free<T> {
        let ValTyp::I32 = typ else { panic!() };
        let op = match self.op {
            BinOp::Plus => refinement::BinOp::Add,
            BinOp::Minus => refinement::BinOp::Sub,
            BinOp::Times => refinement::BinOp::Mul,
            BinOp::Modulo => refinement::BinOp::Rem,
            BinOp::Divide => refinement::BinOp::Div,
            BinOp::Shl => refinement::BinOp::Shl,
            BinOp::Shr => refinement::BinOp::Shr,
        };
        refinement::Free::BinOp {
            l: Rc::new(first(self.l.convert(lookup, ValTyp::I32))),
            r: Rc::new(first(self.r.convert(lookup, ValTyp::I32))),
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
    pub fn convert<T: Clone>(
        &self,
        lookup: &HashMap<String, Nested<T>>,
        typ: ValTyp,
    ) -> refinement::Free<T> {
        let ValTyp::I32 = typ else { panic!() };
        let l = first(self.l.convert(lookup, ValTyp::I32));
        let r = first(self.r.convert(lookup, ValTyp::I32));
        use refinement::BinOp as Op;
        match self.op {
            PropOp::Less => Op::Less.free(l, r),
            PropOp::LessEq => Op::LessEq.free(l, r),
            PropOp::Eq => Op::Eq.free(l, r),
            PropOp::NotEq => Op::NotEq.free(l, r),
            PropOp::And => Op::And.free(l, r),
            PropOp::Or => Op::Or.free(l, r),
            PropOp::MulSafe => Op::MulSafe.free(l, r),
            PropOp::AddSafe => Op::AddSafe.free(l, r),
        }
    }
}

pub fn first<T>(iter: impl IntoIterator<Item = T>) -> T {
    let mut iter = iter.into_iter();
    let first = iter.next().unwrap();
    assert!(iter.next().is_none());
    first
}
