use std::{iter::zip, rc::Rc};

use crate::refinement::{Inj, Thunk};

use super::{BoundExpr, Expr, Fun, Lambda, NegTyp, PosTyp, SubContext, Term, Value, Var};

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
            fun: Rc::new(move |args| NegTyp {
                arg: (self.fun)(args),
                ret: ret.clone(),
            }),
            measured: self.measured,
        }
    }
}

impl Value<Var> {
    fn calc_args<T>(&self, typ: &Fun<T>) -> Vec<Rc<Term>> {
        let mut res = vec![];
        for (inj, obj) in zip_eq(&self.inj, &typ.measured) {
            match inj {
                Inj::Just(idx, val) => {
                    let f_alpha = &obj.f_alpha[*idx];
                    let args = val.calc_args(f_alpha);
                    let (_pos, arg) = (f_alpha.fun)(&args);
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
}

// Value, Head, Expr and BoundExpr are always position independent
// "position independent" only refers to sort indices
impl SubContext {
    // This resolves value determined indices in `p`
    pub fn check_value(&self, v: &Value<Var>, p: &Fun<PosTyp>) {
        let p_args = v.calc_args(p);
        let pos = (p.fun)(&p_args);
        self.verify_props(pos.prop);

        for (thunk, n) in zip_eq(&v.thunk, &pos.thunks) {
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

    // This resolves value determined indices in `n`
    // if `n` is position independent, then the output is also position independent
    pub fn spine(&self, n: &Fun<NegTyp>, s: &Value<Var>) -> Fun<PosTyp> {
        let n_args = s.calc_args(n);
        let neg = (n.fun)(&n_args);
        self.verify_props(neg.arg.prop);

        for (thunk, n) in zip_eq(&s.thunk, &neg.arg.thunks) {
            self.check_thunk(thunk, n);
        }
        neg.ret
    }

    // the result is position independent
    pub fn infer_bound_expr(&self, g: &BoundExpr<Var>) -> Fun<PosTyp> {
        match g {
            BoundExpr::App(idx, proj, s) => {
                let n = idx.infer_thunk(proj);
                self.spine(n, s)
            }
            BoundExpr::Anno(e, negs) => {
                let pos = PosTyp {
                    thunks: negs.clone(),
                    prop: vec![],
                };
                let arg = Var {
                    args: vec![],
                    inner: Rc::new(pos.clone()),
                };
                let p = Fun {
                    tau: vec![],
                    measured: vec![],
                    fun: Rc::new(move |_| pos.clone()),
                };
                self.check_expr_pos(&e.inst(&arg), &p);
                p
            }
        }
    }

    // can we make sure that `n` is always position independent????
    pub fn check_expr(&self, l: &Lambda<Var>, n: &Fun<NegTyp>) {
        let (neg, this) = self.extract(n);
        let var = Var {
            args: zip_eq(neg.terms, n.measured.clone()).collect(),
            inner: Rc::new(neg.inner.arg),
        };
        let e = l.inst(&var);
        this.check_expr_pos(&e, &neg.inner.ret);
    }

    pub fn check_expr_pos(&self, e: &Expr<Var>, p: &Fun<PosTyp>) {
        match e {
            Expr::Return(v) => {
                self.check_value(v, p);
            }
            Expr::Let(g, l) => {
                let bound_p = self.infer_bound_expr(g);
                self.check_expr(l, &bound_p.arrow(p.clone()))
            }
            Expr::Match(idx, proj, pats) => {
                let (term, obj) = idx.infer_inj(proj);

                assert_eq!(pats.len(), obj.f_alpha.len());
                for (i, l) in pats.iter().enumerate() {
                    let match_p = self.unroll_prod_univ(term, obj, &i);
                    self.check_expr(l, &match_p.arrow(p.clone()));
                }
            }
            Expr::Tail(idx, proj, s) => {
                let n = idx.infer_thunk(proj);
                let res = self.spine(n, s);
                self.sub_pos_typ(&res, p);
            }
        }
    }
}
