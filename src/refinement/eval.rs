use std::{
    cmp,
    rc::{Rc, Weak},
};

use crate::parse::{self, desugar::Desugar};

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
                Builtin::Read => {
                    let [ptr] = *arg else { panic!() };
                    vec![self.data[ptr as usize] as i32]
                }
                Builtin::Write => {
                    let [ptr, val] = *arg else { panic!() };
                    self.data[ptr as usize] = val as u8;
                    vec![]
                }
                Builtin::Pack(_, _) => vec![],
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

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;

    // #[test]
    // fn match_test() {
    //     let expr = parse_lambda! { Eval; (val) =>
    //         match val
    //         { return ()}
    //     };
    //     let val = Res::new(0);
    //     let expr = expr.inst_arg(&val);
    //     Memory::default().eval(expr);
    // }

    // #[test]
    // #[ignore = "diverges"]
    // fn diverge() {
    //     let expr = parse_expr! {Eval;
    //         let val@(): () = ();
    //         loop val = ()
    //     };
    //     let expr = Rc::new(expr);
    //     Memory::default().eval(expr);
    // }

    // #[test]
    // fn increment() {
    //     parse_lambda! {Eval; (ptr) =>
    //         let (x) = ptr[0];
    //         ptr[0] = x;
    //         return ()
    //     };
    // }

    // #[test]
    // fn testing() {
    //     #[allow(non_snake_case)]
    //     let MyBool = inductive!(_ = () | ()).leak();

    //     let e = parse_expr! {Var;
    //         let funcs: (
    //             (Nat) -> (Nat),
    //             () -> ()
    //         ) = (
    //             {x =>
    //                 let tmp: (a:Nat, (a) == (x.0)) = (x.0);
    //                 return (tmp.0)},
    //             {_x => return ()}
    //         );

    //         let _res = funcs.1 ();
    //         let data: (MyBool) = (1);

    //         match data.0
    //         {unit => loop unit = ()}
    //         {_y => return () }
    //     };

    //     let ctx = SubContext::default();
    //     ctx.check_expr_pos(&e, &pos_typ!())
    // }

    // #[test]
    // fn zip_lists() {
    //     #[allow(non_snake_case)]
    //     let List = pos_typ!(List = ptr:Nat, (ptr @ () | ptr @ (Nat, List)));
    //     #[allow(non_snake_case)]
    //     let ZippedList = |ptr: &Term| {
    //         inductive!(ZippedList if ptr = () | (Nat, Nat, ptr:Nat, ZippedList(ptr))).leak()
    //     };

    //     let store_cons = pos_typ!(ptr:Nat, ZippedList(ptr)).write();

    //     let func = parse_lambda!(Var;
    //         inputs =>
    //             let rec: ((l:Nat, List(l), r:Nat, List(r)) -> (ptr:Nat, ZippedList(ptr))) = ({args => loop inputs = (args.0, args.1)});
    //             match inputs.0
    //                 {_ => return (0)}
    //                 {cons_l => match inputs.1
    //                     {_ => return (0)}
    //                     {cons_r =>
    //                         let tail = rec.0 (cons_l.1, cons_r.1);
    //                         return (1) // (cons_l.0, cons_r.0, tail.0)
    //                     }
    //                 }
    //     );
    //     let ctx = SubContext::default();
    //     ctx.check_expr(&func, &neg_typ!((List, List) -> (ZippedList)))
    // }

    // #[test]
    // fn last_item() {
    //     #[allow(non_snake_case)]
    //     let Boxes = inductive!(Boxes = (Nat) | (Boxes)).leak();

    //     let func = parse_lambda!(Var;
    //         list => match list.0
    //             {last => return (last.0)}
    //             {boxed => loop list = (boxed.0)}
    //     );

    //     let ctx = SubContext::default();
    //     ctx.check_expr(&func, &neg_typ!((Boxes) -> (Nat)))
    // }
}
