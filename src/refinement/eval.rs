use std::{
    cmp,
    rc::{Rc, Weak},
};

use crate::{desugar::Desugar, parse, refinement::typing::zip_eq};

use super::{builtin::Builtin, BoundExpr, Expr, Free, Lambda, Thunk, Val, Value};

#[derive(Default)]
pub struct Memory {
    data: Vec<u8>,
}

impl Memory {
    pub fn new(data: Vec<u8>) -> Self {
        Self { data }
    }
}

impl Free<i32> {
    pub fn eval(&self) -> i32 {
        match self {
            Free::Just(idx, _size) => *idx as i32,
            Free::Var(local) => *local,
            Free::BinOp { l, r, op } => op.eval(l.eval(), r.eval()),
        }
    }
}

impl Value<i32> {
    pub fn to_vec(&self) -> Vec<i32> {
        self.inj.iter().map(|inj| inj.eval()).collect()
    }
}

impl Val for i32 {
    type Func = Rc<Lambda<i32>>;
    fn make(
        _this: &Desugar<Self>,
        lamb: &Weak<Lambda<Self>>,
        _typ: &parse::types::NegTyp,
    ) -> Self::Func {
        lamb.upgrade().unwrap()
    }
}

impl Memory {
    pub fn eval(&mut self, mut expr: Expr<i32>) -> Vec<i32> {
        loop {
            match &expr {
                Expr::Return(val) => return val.to_vec(),
                Expr::Let(bind, e) => {
                    match bind {
                        BoundExpr::App(func, arg) => {
                            let arg = self.call_func(arg, func);
                            expr = e.inst(&arg).val;
                        }
                        BoundExpr::Cont(_cont, _lamb) => {
                            expr = e.inst(&[]).val;
                        }
                    };
                }
                Expr::Match(local, e) => {
                    // clip index because last branch is the default
                    let idx = cmp::min(local.eval() as usize, e.len() - 1);
                    expr = e[idx].inst(&[]).val;
                }
                Expr::Loop(func, arg) => {
                    let arg = arg.to_vec();
                    expr = func.inst(&arg).val;
                }
            }
        }
    }

    fn call_func(&mut self, arg: &Value<i32>, func: &Thunk<i32>) -> Vec<i32> {
        let arg = arg.to_vec();
        match func {
            Thunk::Local(func) => {
                let expr = func.inst(&arg).val;
                self.eval(expr)
            }
            Thunk::Builtin(builtin) => match builtin {
                Builtin::Read8 => {
                    let [ptr] = *arg else { panic!() };
                    vec![self.data[ptr as usize] as i32]
                }
                Builtin::Read32 => {
                    let [ptr] = *arg else { panic!() };
                    let data = &self.data[ptr as usize..][..4];
                    let val = i32::from_le_bytes(data.try_into().unwrap());
                    vec![val]
                }
                Builtin::Write8 => {
                    let [ptr, val] = *arg else { panic!() };
                    self.data[ptr as usize] = val as u8;
                    vec![]
                }
                Builtin::Write32 => {
                    let [ptr, val] = *arg else { panic!() };
                    zip_eq(&mut self.data[ptr as usize..], val.to_le_bytes())
                        .for_each(|(d, s)| *d = s);
                    vec![]
                }
                Builtin::Pack(_) => vec![],
                Builtin::Alloc => {
                    let [bytes] = *arg else { panic!() };
                    let start = self.data.len();
                    self.data.resize(start + bytes as usize, 0);
                    vec![start as i32]
                }
            },
        }
    }
}
