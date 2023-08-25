use std::{iter::zip, rc::Rc};

use crate::refinement::{Inj, Thunk};

use super::{
    BoundExpr, Expr, Fun, Lambda, Measured, NegTyp, PosTyp, Prop, SubContext, Unsolved, Value, Var,
};

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
            fun: Rc::new(move |args| {
                let (arg, props) = (self.fun)(args);
                let n = NegTyp {
                    arg,
                    ret: ret.clone(),
                };
                (n, props)
            }),
        }
    }
}

// Value, Head, Expr and BoundExpr are always position independent
// "position independent" only refers to sort indices
impl SubContext {
    // This resolves value determined indices in `p`
    pub fn check_value(&self, v: &Value<Var>, p: &Unsolved<PosTyp>, props: Vec<Rc<Prop>>) {
        for (inj, obj) in zip_eq(&v.inj, &p.inner.measured) {
            self.check_inj(inj, obj);
        }
        p.assert_resolved();
        self.verify_props(props);

        for (thunk, n) in zip_eq(&v.thunk, &p.inner.thunks) {
            self.check_thunk(thunk, n);
        }
    }

    pub fn check_inj(&self, inj: &Inj<Var>, obj: &Measured) {
        match inj {
            Inj::Just(i, v) => {
                let (p, props) = self.unroll_prod(obj, i);
                self.check_value(v, &p, props);
            }
            Inj::Var(idx, proj) => {
                let var = idx.infer_inj(proj);
                self.eq_functor(var, obj);
            }
        }
    }

    pub fn check_thunk(&self, thunk: &Thunk<Var>, n: &Fun<NegTyp>) {
        match thunk {
            Thunk::Just(e) => self.check_expr(e, n),
            Thunk::Var(idx, proj) => {
                let m = idx.infer_thunk(proj);
                let (n, this) = self.extract(n);
                this.sub_neg_type(m, &n);
            }
        }
    }

    // This resolves value determined indices in `n`
    // if `n` is position independent, then the output is also position independent
    pub fn spine(&self, n: &Fun<NegTyp>, s: &Value<Var>) -> Fun<PosTyp> {
        let (n, props) = self.extract_evar(n);

        for (inj, obj) in zip_eq(&s.inj, &n.inner.arg.measured) {
            self.check_inj(inj, obj);
        }
        n.assert_resolved();
        self.verify_props(props);

        for (thunk, n) in zip_eq(&s.thunk, &n.inner.arg.thunks) {
            self.check_thunk(thunk, n);
        }

        n.inner.ret
    }

    // the result is position independent
    pub fn infer_bound_expr(&self, g: &BoundExpr<Var>) -> Fun<PosTyp> {
        match g {
            BoundExpr::App(idx, proj, s) => {
                let n = idx.infer_thunk(proj);
                self.spine(n, s)
            }
            BoundExpr::Anno(e, negs) => {
                let negs = negs.clone();
                let pos = move || PosTyp {
                    measured: vec![],
                    thunks: negs.clone(),
                };
                let arg = Var(Rc::new((pos)()));
                let p = Fun {
                    tau: vec![],
                    fun: Rc::new(move |_| ((pos)(), vec![])),
                };
                self.check_expr_pos(&e.inst(&arg), &p);
                p
            }
        }
    }

    // can we make sure that `n` is always position independent????
    pub fn check_expr(&self, l: &Lambda<Var>, n: &Fun<NegTyp>) {
        let (n, this) = self.extract(n);
        let e = l.inst(&Var(Rc::new(n.arg)));
        this.check_expr_pos(&e, &n.ret);
    }

    pub fn check_expr_pos(&self, e: &Expr<Var>, p: &Fun<PosTyp>) {
        match e {
            Expr::Return(v) => {
                let (p, props) = self.extract_evar(p);
                self.check_value(v, &p, props);
            }
            Expr::Let(g, l) => {
                let bound_p = self.infer_bound_expr(g);
                self.check_expr(l, &bound_p.arrow(p.clone()))
            }
            Expr::Match(idx, proj, pats) => {
                let obj = idx.infer_inj(proj);

                assert_eq!(pats.len(), obj.f_alpha.len());
                for (i, l) in pats.iter().enumerate() {
                    let match_p = self.unroll_prod_univ(obj, &i);
                    self.check_expr(l, &match_p.arrow(p.clone()));
                }
            }
            Expr::Tail(idx, proj, s) => {
                let n = idx.infer_thunk(proj);
                let q = self.spine(n, s);
                let (q, this) = self.extract(&q);
                this.sub_pos_typ(&q, p);
            }
        }
    }
}
