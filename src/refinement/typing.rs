use std::{iter::zip, rc::Rc};

use crate::refinement::{Inj, Thunk};

use super::{BoundExpr, Expr, Fun, FuncRef, Lambda, NegTyp, PosTyp, Sort, SubContext, Term, Value};

#[derive(Clone)]
pub struct Var {
    args: Vec<(Rc<Term>, Sort)>,
    inner: Rc<PosTyp>,
    rec: Fun<NegTyp>,
}

impl Var {
    fn get_term(&self, proj: usize) -> Rc<Term> {
        self.infer_inj(&proj).0.clone()
    }
}

impl Var {
    fn infer_inj(&self, proj: &usize) -> &(Rc<Term>, Sort) {
        &self.args[*proj]
    }

    fn infer_thunk(&self, proj: &usize) -> &Fun<NegTyp> {
        &self.inner.thunks[*proj]
    }
}

impl FuncRef<Var> {
    fn infer_thunk(&self) -> Fun<NegTyp> {
        match self {
            FuncRef::Local(var, proj) => var.inner.thunks[*proj].clone(),
            FuncRef::Builtin(builtin) => builtin.infer(),
        }
    }
}

pub fn zip_eq<A: IntoIterator, B: IntoIterator>(
    a: A,
    b: B,
) -> impl Iterator<Item = (A::Item, B::Item)>
where
    A::IntoIter: ExactSizeIterator,
    B::IntoIter: ExactSizeIterator,
{
    let (a_iter, b_iter) = (a.into_iter(), b.into_iter());
    assert_eq!(a_iter.len(), b_iter.len());
    zip(a_iter, b_iter)
}

impl Fun<PosTyp> {
    pub fn arrow(self, ret: Fun<PosTyp>) -> Fun<NegTyp> {
        Fun {
            tau: self.tau,
            fun: Rc::new(move |args, heap| NegTyp {
                arg: (self.fun)(args, heap),
                ret: ret.clone(),
            }),
        }
    }
}

impl SubContext {
    fn calc_args(&self, val: &Value<Var>) -> Vec<Rc<Term>> {
        let mut res = vec![];
        for inj in &val.inj {
            match inj {
                Inj::Just(idx) => {
                    let arg = Rc::new(Term::Nat(*idx));
                    res.push(arg);
                }
                Inj::Var(idx, proj) => {
                    let (arg, _obj) = idx.infer_inj(proj);
                    res.push(arg.clone())
                }
            }
        }
        res
    }

    // This resolves value determined indices in `p`
    pub fn check_value(&mut self, v: &Value<Var>, p: &Fun<PosTyp>) {
        let p_args = self.calc_args(v);
        let typ = self.with_terms(p, &p_args);

        for (thunk, n) in zip_eq(&v.thunk, &typ.thunks) {
            self.check_thunk(thunk, n);
        }
    }

    pub fn check_thunk(&self, thunk: &Thunk<Var>, n: &Fun<NegTyp>) {
        match thunk {
            Thunk::Just(e) => self.check_expr(e, n),
            Thunk::Var(idx, proj) => {
                let m = idx.infer_thunk(proj);
                self.sub_neg_type(m, n);
            }
        }
    }

    pub fn spine(&mut self, n: &Fun<NegTyp>, s: &Value<Var>) -> Fun<PosTyp> {
        let n_args = self.calc_args(s);
        let typ = self.with_terms(n, &n_args);

        for (thunk, n) in zip_eq(&s.thunk, &typ.arg.thunks) {
            self.check_thunk(thunk, n);
        }
        typ.ret
    }

    pub fn check_expr(&self, l: &Lambda<Var>, n: &Fun<NegTyp>) {
        let (neg, mut this) = self.extract(n);
        let var = Var {
            args: zip_eq(neg.terms, n.tau.clone()).collect(),
            inner: Rc::new(neg.inner.arg),
            rec: n.clone(),
        };
        let e = l.inst(&var);
        this.check_expr_pos(&e, &neg.inner.ret);
    }

    pub fn check_expr_pos(&mut self, e: &Expr<Var>, p: &Fun<PosTyp>) {
        match e {
            Expr::Return(v) => {
                self.check_value(v, p);
                // leaking resources is not allowed
                assert!(self.alloc.is_empty(), "can not leak memory");
            }
            Expr::Let(g, l) => {
                let bound_p = match g {
                    BoundExpr::App(func, s) => {
                        let n = func.infer_thunk();
                        self.spine(&n, s)
                    }
                    BoundExpr::Anno(e, p) => {
                        self.check_value(e, p);
                        p.clone()
                    }
                };
                self.check_expr(l, &bound_p.arrow(p.clone()))
            }
            Expr::Match(idx, proj, pats) => {
                let (term, _tau) = idx.infer_inj(proj);

                for (i, l) in pats.iter().enumerate() {
                    // we want to preserve resources between branches
                    let this = self.clone();
                    let match_p = this.unroll_prod_univ(term, i);
                    this.check_expr(l, &match_p.arrow(p.clone()));
                }
            }
            Expr::Loop(idx, s) => {
                let n = &idx.rec;
                let res = self.spine(n, s);
                self.sub_pos_typ(&res, p);
            }
        }
    }
}
