use std::rc::Rc;

use super::{BoundExpr, Expr, Inj, Lambda, Term, Thunk, Value};

#[derive(Clone)]
struct Eval {
    res: Res,
    rec: Lambda<Eval>,
}

impl Eval {
    fn get_term(&self, proj: usize) -> Rc<Term> {
        self.res.get_term(proj)
    }
}

#[derive(Clone, Default)]
struct Res {
    inj: Vec<usize>,
    thunks: Vec<Lambda<Eval>>,
}

impl Res {
    fn make_eval(&self, rec: &Lambda<Eval>) -> Eval {
        Eval {
            res: self.clone(),
            rec: rec.clone(),
        }
    }

    fn get_term(&self, proj: usize) -> Rc<Term> {
        let idx = self.inj[proj];
        let res = Term::Nat(idx);
        Rc::new(res)
    }
}

impl Lambda<Eval> {
    fn inst_arg(&self, arg: &Res) -> Rc<Expr<Eval>> {
        let arg = arg.make_eval(self);
        Rc::new(self.inst(&arg))
    }
}

impl Eval {
    fn get_thunk(&self, proj: &usize) -> &Lambda<Eval> {
        &self.res.thunks[*proj]
    }

    fn get_inj(&self, proj: &usize) -> &usize {
        &self.res.inj[*proj]
    }
}

impl Res {
    pub fn from_val(val: &Value<Eval>) -> Self {
        let inj = val.inj.iter().map(|inj| match inj {
            Inj::Just(idx) => *idx,
            Inj::Var(var, proj) => *var.get_inj(proj),
        });
        let thunks = val.thunk.iter().map(|thun| match thun {
            Thunk::Just(lamb) => lamb.clone(),
            Thunk::Var(var, proj) => var.get_thunk(proj).clone(),
        });
        Self {
            inj: inj.collect(),
            thunks: thunks.collect(),
        }
    }
}

impl Expr<Eval> {
    pub fn eval(mut self: Rc<Self>) -> Res {
        loop {
            match self.as_ref() {
                Expr::Return(val) => return Res::from_val(val),
                Expr::Let(bind, e) => {
                    let arg = bind.eval();
                    self = e.inst_arg(&arg);
                }
                Expr::Match(var, proj, e) => {
                    let idx = var.get_inj(proj);
                    self = e[*idx].inst_arg(&Default::default());
                }
                Expr::Loop(var, arg) => {
                    let arg = Res::from_val(arg);
                    self = var.rec.inst_arg(&arg);
                }
            }
        }
    }
}

impl BoundExpr<Eval> {
    pub fn eval(&self) -> Res {
        match self {
            BoundExpr::App(var, proj, arg) => {
                let arg = Res::from_val(arg);
                var.get_thunk(proj).inst_arg(&arg).eval()
            }
            BoundExpr::Anno(val, _pos) => Res::from_val(val),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::refinement::{SubContext, Var};

    use super::*;

    #[test]
    fn match_test() {
        let expr = parse_lambda! { Eval; val =>
            match val.0
            {_thing => return ()}
        };
        let val = Res {
            inj: vec![0],
            thunks: vec![],
        };
        expr.inst_arg(&val).eval();
    }

    #[test]
    fn diverge() {
        let expr = parse_expr! {Eval;
            let rec: () = ();
            loop rec = ()
        };
        Rc::new(expr).eval();
    }

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
    //     let ZippedList = |ptr: &Rc<Term>| {
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
