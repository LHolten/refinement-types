use std::rc::Rc;

use super::{BoundExpr, Expr, Inj, Lambda, Thunk, Value};

#[derive(Clone)]
struct Eval {
    inj: Vec<(usize, Eval)>,
    thunks: Vec<Lambda<Eval>>,
}

impl Eval {
    pub fn get_thunk(&self, proj: &usize) -> &Lambda<Eval> {
        &self.thunks[*proj]
    }

    pub fn get_inj(&self, proj: &usize) -> &(usize, Eval) {
        &self.inj[*proj]
    }

    pub fn from_val(val: &Value<Self>) -> Self {
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
    pub fn eval(mut self: Rc<Self>) -> Eval {
        loop {
            match self.as_ref() {
                Expr::Return(val) => return Eval::from_val(val),
                Expr::Let(bind, e) => {
                    let arg = bind.eval();
                    self = Rc::new(e.inst(&arg))
                }
                Expr::Match(var, proj, e) => {
                    let (idx, val) = var.get_inj(proj);
                    self = Rc::new(e[*idx].inst(val))
                }
                Expr::Tail(var, proj, arg) => {
                    let arg = Eval::from_val(arg);
                    self = Rc::new(var.get_thunk(proj).inst(&arg));
                }
            }
        }
    }
}

impl BoundExpr<Eval> {
    pub fn eval(&self) -> Eval {
        match self {
            BoundExpr::App(var, proj, arg) => {
                let arg = Eval::from_val(arg);
                let e = var.get_thunk(proj).inst(&arg);
                Rc::new(e).eval()
            }
            BoundExpr::Anno(e, negs) => {
                let arg = Eval {
                    inj: vec![],
                    thunks: (0..negs.len())
                        .map(|proj| {
                            let this = BoundExpr::Anno(e.clone(), negs.clone());
                            Lambda(Rc::new(move |arg| this.eval().get_thunk(&proj).inst(arg)))
                        })
                        .collect(),
                };
                Rc::new(e.inst(&arg)).eval()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;

    #[test]
    fn diverge() {
        let bind = BoundExpr::Anno(
            Lambda::<Eval>::new(|rec| {
                let rec = rec.clone();
                Expr::Return(Rc::new(Value {
                    thunk: vec![Thunk::Just(Lambda::new(move |_| {
                        Expr::Tail(rec.clone(), 0, Rc::new(Value::default()))
                    }))],
                    inj: vec![],
                }))
            }),
            vec![neg_typ!(() -> ())],
        );
        bind.eval();
        let e = Expr::Let(
            bind,
            Lambda::<Eval>::new(|inf| {
                Expr::Let(
                    BoundExpr::App(inf.clone(), 0, Rc::new(Value::default())),
                    Lambda::<Eval>::new(|res| Expr::Match(res.clone(), 0, vec![])),
                )
            }),
        );
        Rc::new(e).eval();
    }
}
