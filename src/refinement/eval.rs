use std::rc::Rc;

use super::{BoundExpr, Expr, Inj, Lambda, Thunk, Value};

#[derive(Clone)]
struct Eval {
    res: Res,
    rec: Lambda<Eval>,
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
                Expr::Tail(var, arg) => {
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
            BoundExpr::Anno(e, _pos) => e.clone().eval(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

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
            let rec: () = (return ());
            tail rec ()
        };
        Rc::new(expr).eval();
    }
}
