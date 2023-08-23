use std::rc::Rc;

use super::{BoundExpr, Expr, Inj, Lambda, Thunk, Value};

struct Eval(Rc<Value<Eval>>);

impl Eval {
    pub fn get_thunk(&self, proj: &usize) -> &Lambda<Eval> {
        match &self.0.thunk[*proj] {
            Thunk::Just(val) => val,
            Thunk::Var(var, proj) => var.get_thunk(proj),
        }
    }

    pub fn get_inj(&self, proj: &usize) -> (usize, Eval) {
        match &self.0.inj[*proj] {
            Inj::Just(idx, val) => (*idx, Eval(val.clone())),
            Inj::Var(var, proj) => var.get_inj(proj),
        }
    }
}

impl Expr<Eval> {
    pub fn eval(&self) -> Eval {
        match self {
            Expr::Return(val) => Eval(val.clone()),
            Expr::Let(bind, e) => {
                let arg = bind.eval();
                e.inst(&arg).eval()
            }
            Expr::Match(var, proj, e) => {
                let (idx, val) = var.get_inj(proj);
                e[idx].inst(&val).eval()
            }
        }
    }
}

impl BoundExpr<Eval> {
    pub fn eval(&self) -> Eval {
        match self {
            BoundExpr::App(var, proj, arg) => {
                let arg = Eval(arg.clone());
                var.get_thunk(proj).inst(&arg).eval()
            }
            BoundExpr::Anno(e, _typ) => e.eval(),
        }
    }
}
