use std::rc::Rc;

use super::{BoundExpr, Expr, Inj, Lambda, Term, Thunk, Value};

#[derive(Clone)]
struct Eval {
    res: Res,
    rec: Lambda<Eval>,
}

impl Eval {
    fn get_term(&self, proj: usize) -> Rc<Term> {
        Rc::new(self.res.get_term(proj))
    }
}

#[derive(Clone, Default)]
struct Res {
    inj: Vec<(usize, Res)>,
    thunks: Vec<Lambda<Eval>>,
}

impl Res {
    fn make_eval(&self, rec: &Lambda<Eval>) -> Eval {
        Eval {
            res: self.clone(),
            rec: rec.clone(),
        }
    }

    fn get_term(&self, proj: usize) -> Term {
        let (idx, ref val) = self.inj[proj];
        Term::Inj(idx, (0..val.inj.len()).map(|i| val.get_term(i)).collect())
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

    fn get_inj(&self, proj: &usize) -> &(usize, Res) {
        &self.res.inj[*proj]
    }
}

impl Res {
    pub fn from_val(val: &Value<Eval>) -> Self {
        let inj = val.inj.iter().map(|inj| match inj {
            Inj::Just(idx, val) => (*idx, Self::from_val(val)),
            Inj::Var(var, proj) => var.get_inj(proj).clone(),
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
                    let (idx, val) = var.get_inj(proj);
                    self = e[*idx].inst_arg(val);
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
            inj: vec![(0, Res::default())],
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

    #[test]
    fn testing() {
        let e = parse_expr! {Var;
            let funcs: (
                (a) -> (b, (a) == (b)),
                () -> ()
            ) = (
                {x =>
                    let tmp: (y, (y) == (x.0)) = (x.0);
                    return (tmp.0)},
                {_x => return ()}
            );
            let _diverge: (() -> ()) = (
                {rec => loop rec = ()}
            );
            let _unit = funcs.1 ();

            let data: (_) = (0());

            match data.0
            // {x => loop unit = ()}
            {_y => return () }
        };

        let ctx = SubContext::default();
        ctx.check_expr_pos(&e, &pos_typ!())
    }
}
