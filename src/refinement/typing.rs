use std::{iter::zip, rc::Rc};

use crate::refinement::{Inj, Sort, Thunk, VarContext};

use super::{
    BoundExpr, Constraint, ContextPart, Expr, ExtendedConstraint, FullContext, Fun, Measured,
    NegTyp, PosTyp, Prop, Term, Unsolved, Value,
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

// Value, Head, Expr and BoundExpr are always position independent
// "position independent" only refers to sort indices
impl FullContext {
    // That is the only way to make it relocatable
    // I don't know if we can do this by wrapping..
    pub fn add_pos(&self, p: &Fun<PosTyp>) -> Self {
        let (p, theta) = self.extract(p);
        self.add_pos_theta(p, theta)
    }

    pub fn add_pos_theta(&self, p: PosTyp, theta: Vec<ContextPart>) -> Self {
        let mut this = self.extend_univ(theta);
        this.var = Rc::new(VarContext::Cons {
            typ: Rc::new(p),
            next: this.var,
        });
        this
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

    // global
    pub fn extend_univ(&self, theta: Vec<ContextPart>) -> Self {
        let mut this = self.clone();
        this.sub = this.sub.extend_univ(theta);
        this
    }

    pub fn new_evar(&self, tau: &Sort) -> (Self, Rc<Term>) {
        let (sub, evar) = self.sub.new_evar(tau);
        let this = Self {
            sub,
            var: self.var.clone(),
        };
        (this, evar)
    }

    // This resolves value determined indices in `p`
    pub fn check_value(
        &self,
        v: &Value,
        p: &Unsolved<PosTyp>,
        props: Vec<Rc<Prop>>,
    ) -> ExtendedConstraint {
        let mut xi = ExtendedConstraint::default();
        for (inj, obj) in zip_eq(&v.inj, &p.inner.measured) {
            xi = xi & self.check_inj(inj, obj);
        }
        p.assert_resolved();

        for (thunk, n) in zip_eq(&v.thunk, &p.inner.thunks) {
            xi = xi & self.check_thunk(thunk, n);
        }

        for phi in props {
            xi = xi.and_prop(&phi)
        }
        xi
    }

    pub fn infer_inj(&self, idx: &usize, proj: &usize) -> &Measured {
        &self.get_pos(idx).measured[*proj]
    }

    pub fn check_inj(&self, inj: &Inj, obj: &Measured) -> ExtendedConstraint {
        match inj {
            Inj::Just(i, v) => {
                let (p, props) = self.unroll_prod(obj, i);
                self.check_value(v, &p, props)
            }
            Inj::Var(idx, proj) => {
                let var = self.infer_inj(idx, proj);
                assert_eq!(var, obj);
                obj.term.instantiate(&var.term);
                ExtendedConstraint::default()
            }
        }
    }

    pub fn infer_thunk(&self, idx: &usize, proj: &usize) -> &Fun<NegTyp> {
        &self.get_pos(idx).thunks[*proj]
    }

    pub fn check_thunk(&self, thunk: &Thunk, n: &Fun<NegTyp>) -> ExtendedConstraint {
        match thunk {
            Thunk::Just(e) => Rc::new(Constraint::Check(e.clone(), n.clone())).extend(&[]),
            Thunk::Var(idx, proj) => {
                let m = self.infer_thunk(idx, proj);
                Rc::new(Constraint::SubNegTyp(m, n.clone())).extend(&[])
            }
        }
    }

    // This resolves value determined indices in `n`
    // if `n` is position independent, then the output is also position independent
    pub fn spine(&self, n: &Fun<NegTyp>, s: &Value) -> (Fun<PosTyp>, ExtendedConstraint) {
        let (n, props) = self.extract_evar(n);
        let mut xi = ExtendedConstraint::default();

        for (inj, obj) in zip_eq(&s.inj, &n.inner.arg.measured) {
            xi = xi & self.check_inj(inj, obj);
        }
        n.assert_resolved();

        for (thunk, n) in zip_eq(&s.thunk, &n.inner.arg.thunks) {
            xi = xi & self.check_thunk(thunk, n);
        }

        for phi in props {
            xi = xi.and_prop(&phi)
        }
        (n.inner.ret.clone(), xi)
    }

    // the result is position independent
    pub fn infer_bound_expr(&self, g: &BoundExpr) -> Fun<PosTyp> {
        match g {
            BoundExpr::App(idx, proj, s) => {
                let n = self.infer_thunk(idx, proj);
                let (p, xi) = self.spine(n, s);
                self.verify(&xi.w);
                p
            }
            BoundExpr::Anno(e, ret) => {
                let fun = Rc::new(|_| {
                    let n = NegTyp {
                        arg: PosTyp::default(),
                        ret: ret.clone(),
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
        let (n, theta) = self.extract(n);
        let this = self.add_pos_theta(n.arg, theta);
        this.check_expr_pos(e, &n.ret);
    }

    pub fn check_expr_pos(&self, e: &Expr, p: &Fun<PosTyp>) {
        match e {
            Expr::Return(v) => {
                let (p, props) = self.extract_evar(p);
                let xi = self.check_value(v, &p, props);
                self.verify(&xi.w);
            }
            Expr::Let(g, e) => {
                let bound_p = self.infer_bound_expr(g);
                self.add_pos(&bound_p).check_expr_pos(e, p)
            }
            Expr::Match(idx, proj, pats) => {
                let obj = self.infer_inj(idx, proj);

                assert_eq!(pats.len(), obj.f_alpha.len());
                for (i, e) in pats.iter().enumerate() {
                    // we ignore the constraint from unrolling
                    let (match_p, theta) = self.unroll_prod_univ(obj, &i);
                    self.add_pos_theta(match_p, theta).check_expr_pos(e, p);
                }
            }
        }
    }
}
