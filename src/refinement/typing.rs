use std::{iter::zip, rc::Rc};

use crate::refinement::{Inj, Thunk, VarContext};

use super::{BoundExpr, Expr, FullContext, Fun, Measured, NegTyp, PosTyp, Prop, Unsolved, Value};

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

// Value, Head, Expr and BoundExpr are always position independent
// "position independent" only refers to sort indices
impl FullContext {
    // That is the only way to make it relocatable
    // I don't know if we can do this by wrapping..
    pub fn add_pos(&self, p: &Fun<PosTyp>) -> Self {
        let (p, this) = self.extract(p);
        this.add_pos_theta(p)
    }

    pub fn add_pos_theta(mut self, p: PosTyp) -> Self {
        self.var = Rc::new(VarContext::Cons {
            typ: Rc::new(p),
            next: self.var,
        });
        self
    }

    // the returned type is position independent
    pub fn get_pos(&self, x: &usize) -> &PosTyp {
        let mut res = &self.var;
        for _ in 0..*x {
            let VarContext::Cons { typ: _, next } = res.as_ref() else {
                panic!()
            };
            res = next;
        }
        let VarContext::Cons { typ, next: _ } = res.as_ref() else {
            panic!()
        };
        typ
    }

    pub fn extract<T>(&self, n: &Fun<T>) -> (T, Self) {
        let (val, sub) = self.sub.extract(n);
        let this = Self {
            sub,
            var: self.var.clone(),
        };
        (val, this)
    }

    // This resolves value determined indices in `p`
    pub fn check_value(&self, v: &Value, p: &Unsolved<PosTyp>, props: Vec<Rc<Prop>>) {
        for (inj, obj) in zip_eq(&v.inj, &p.inner.measured) {
            self.check_inj(inj, obj);
        }
        p.assert_resolved();
        self.verify_props(props);

        for (thunk, n) in zip_eq(&v.thunk, &p.inner.thunks) {
            self.check_thunk(thunk, n);
        }
    }

    pub fn infer_inj(&self, idx: &usize, proj: &usize) -> &Measured {
        &self.get_pos(idx).measured[*proj]
    }

    pub fn check_inj(&self, inj: &Inj, obj: &Measured) {
        match inj {
            Inj::Just(i, v) => {
                let (p, props) = self.unroll_prod(obj, i);
                self.check_value(v, &p, props);
            }
            Inj::Var(idx, proj) => {
                let var = self.infer_inj(idx, proj);
                self.eq_functor(var, obj);
            }
        }
    }

    pub fn infer_thunk(&self, idx: &usize, proj: &usize) -> &Fun<NegTyp> {
        &self.get_pos(idx).thunks[*proj]
    }

    pub fn check_thunk(&self, thunk: &Thunk, n: &Fun<NegTyp>) {
        match thunk {
            Thunk::Just(e) => self.check_expr(e, n),
            Thunk::Var(idx, proj) => {
                let m = self.infer_thunk(idx, proj);
                let (n, this) = self.extract(n);
                this.sub_neg_type(m, &n);
            }
        }
    }

    // This resolves value determined indices in `n`
    // if `n` is position independent, then the output is also position independent
    pub fn spine(&self, n: &Fun<NegTyp>, s: &Value) -> Fun<PosTyp> {
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
    pub fn infer_bound_expr(&self, g: &BoundExpr) -> Fun<PosTyp> {
        match g {
            BoundExpr::App(idx, proj, s) => {
                let n = self.infer_thunk(idx, proj);
                self.spine(n, s)
            }
            BoundExpr::Anno(e, ret) => {
                let move_ret = ret.clone();
                let fun = Rc::new(move |_: &_| {
                    let n = NegTyp {
                        arg: PosTyp::default(),
                        ret: move_ret.clone(),
                    };
                    (n, vec![])
                });
                self.check_expr(e, &Fun { tau: vec![], fun });
                ret.clone()
            }
        }
    }

    // can we make sure that `n` is always position independent????
    pub fn check_expr(&self, e: &Expr, n: &Fun<NegTyp>) {
        let (n, this) = self.extract(n);
        let this = this.add_pos_theta(n.arg);
        this.check_expr_pos(e, &n.ret);
    }

    pub fn check_expr_pos(&self, e: &Expr, p: &Fun<PosTyp>) {
        match e {
            Expr::Return(v) => {
                let (p, props) = self.extract_evar(p);
                self.check_value(v, &p, props);
            }
            Expr::Let(g, e) => {
                let bound_p = self.infer_bound_expr(g);
                self.add_pos(&bound_p).check_expr_pos(e, p)
            }
            Expr::Match(idx, proj, pats) => {
                let obj = self.infer_inj(idx, proj);

                assert_eq!(pats.len(), obj.f_alpha.len());
                for (i, e) in pats.iter().enumerate() {
                    let match_p = self.unroll_prod_univ(obj, &i);
                    self.add_pos(&match_p).check_expr_pos(e, p);
                }
            }
        }
    }
}
