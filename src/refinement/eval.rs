use std::{cmp, rc::Rc};

use super::{builtin::Builtin, BoundExpr, Expr, Free, Lambda, Local, Thunk, Value};

#[derive(Clone)]
pub struct Eval {
    res: Res,
    rec: Lambda<Eval>,
}

impl Eval {
    fn get_term(&self, proj: usize) -> i64 {
        self.res.get_term(proj)
    }
}

#[derive(Clone, Default)]
pub struct Res {
    pub inj: Vec<i64>,
}

#[derive(Default)]
pub struct Memory {
    data: Vec<i64>,
}

impl Res {
    fn new(val: i64) -> Self {
        Self { inj: vec![val] }
    }

    pub fn make_eval(&self, rec: &Lambda<Eval>) -> Eval {
        Eval {
            res: self.clone(),
            rec: rec.clone(),
        }
    }

    fn get_term(&self, proj: usize) -> i64 {
        self.inj[proj]
    }
}

impl Lambda<Eval> {
    fn inst_arg(&self, arg: &Res) -> Rc<Expr<Eval>> {
        let arg = arg.make_eval(self);
        Rc::new(self.inst(&arg))
    }
}

impl Local<Eval> {
    fn get_thunk(&self) -> &Lambda<Eval> {
        // &self.0.res.thunks[self.1]
        panic!()
    }

    fn get_inj(&self) -> i64 {
        self.0.res.inj[self.1]
    }
}

impl Free<Local<Eval>> {
    pub fn eval(&self) -> i64 {
        match self {
            Free::Just(idx, _size) => *idx,
            Free::Var(local) => local.get_inj(),
            Free::BinOp { l, r, op } => op.eval(l.eval(), r.eval()),
        }
    }
}

impl Res {
    pub fn from_val(val: &Value<Eval>) -> Self {
        let inj = val.inj.iter().map(|inj| inj.eval());
        Self { inj: inj.collect() }
    }
}

impl Memory {
    pub fn eval(&mut self, mut expr: Rc<Expr<Eval>>) -> Res {
        loop {
            match expr.as_ref() {
                Expr::Return(val) => return Res::from_val(val),
                Expr::Let(bind, e) => {
                    match bind {
                        BoundExpr::App(func, arg) => {
                            let arg = self.call_func(arg, func);
                            expr = e.inst_arg(&arg);
                        }
                        BoundExpr::Cont(cont, _neg) => {
                            let eval = Eval {
                                res: Res::default(),
                                rec: cont.to_owned(),
                            };
                            expr = Rc::new((e.0)(&eval));
                        }
                    };
                }
                Expr::Match(local, e) => {
                    // clip index because last branch is the default
                    let idx = cmp::min(local.eval() as usize, e.len() - 1);
                    expr = e[idx].inst_arg(&Default::default());
                }
                Expr::Loop(var, arg) => {
                    let arg = Res::from_val(arg);
                    expr = var.rec.inst_arg(&arg);
                }
            }
        }
    }

    fn call_func(&mut self, arg: &Rc<Value<Eval>>, func: &Thunk<Eval>) -> Res {
        let arg = Res::from_val(arg);
        match func {
            Thunk::Local(local) => {
                let func = local.get_thunk().inst_arg(&arg);
                self.eval(func)
            }
            Thunk::Builtin(builtin) => match builtin {
                Builtin::Read => {
                    let [ptr] = *arg.inj else { panic!() };
                    Res::new(self.data[ptr as usize])
                }
                Builtin::Write => {
                    let [ptr, val] = *arg.inj else { panic!() };
                    self.data[ptr as usize] = val;
                    Res::default()
                }
                Builtin::Pack(_, _) => Res::default(),
                Builtin::Alloc => todo!(),
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
