use std::{iter::zip, rc::Rc};

use crate::refinement::{constraint, Context, SubContext};

use super::{
    BaseFunctor, Constraint, ContextPart, ExtendedConstraint, NegTyp, PosTyp, ProdFunctor,
};

impl SubContext {
    pub fn extend_univ(&self, theta: Vec<ContextPart>) -> Self {
        let mut next = self.assume.clone();
        let mut univ = self.univ;
        for part in theta {
            match part {
                ContextPart::Assume(phi) => next = Rc::new(Context::Assume { phi, next }),
                ContextPart::Free => univ += 1,
            }
        }
        Self {
            exis: self.exis,
            univ,
            assume: next,
        }
    }

    // can we make this position independent into position independent??
    pub fn extract_neg(&self, n: &Rc<NegTyp>) -> (Rc<NegTyp>, Vec<ContextPart>) {
        match n.as_ref() {
            NegTyp::Implies(phi, n) => {
                let (n, mut theta) = self.extract_neg(n);
                theta.push(ContextPart::Assume(phi.clone()));
                (n, theta)
            }
            NegTyp::Forall(n) => {
                // we keep `n` positionally independent
                let (this, uvar) = self.new_uvar(&n.tau);
                let n = (n.fun)(&uvar);
                let (n, mut theta) = this.extract_neg(&n);
                theta.push(ContextPart::Free);
                (n, theta)
            }
            NegTyp::Fun(p, n) => {
                let (p, mut theta_p) = self.extract_pos(p);
                let (n, theta_n) = self.extract_neg(n);
                theta_p.extend(theta_n);
                (Rc::new(NegTyp::Fun(p, n)), theta_p)
            }
            _ => (n.clone(), vec![]),
        }
    }

    pub fn extract_pos(&self, p: &Rc<PosTyp>) -> (Rc<PosTyp>, Vec<ContextPart>) {
        match p.as_ref() {
            PosTyp::Refined(p, phi) => {
                let (p, mut theta) = self.extract_pos(p);
                theta.push(ContextPart::Assume(phi.clone()));
                (p, theta)
            }
            PosTyp::Exists(p) => {
                let (this, uvar) = self.new_uvar(&p.tau);
                let p = (p.fun)(&uvar);
                let (p, mut theta) = this.extract_pos(&p);
                theta.push(ContextPart::Free);
                (p, theta)
            }
            PosTyp::Prod(p) => {
                let mut theta1 = vec![];
                let mut p1 = vec![];
                for p2 in p {
                    let (p2, theta2) = self.extract_pos(p2);
                    p1.push(p2);
                    theta1.extend(theta2);
                }
                (Rc::new(PosTyp::Prod(p1)), theta1)
            }
            _ => (p.clone(), vec![]),
        }
    }

    pub fn sub_base_functor(&self, f: &BaseFunctor, g: &BaseFunctor) -> ExtendedConstraint {
        match (f, g) {
            (BaseFunctor::Pos(p), BaseFunctor::Pos(q)) => self.sub_pos_typ(p, q),
            (BaseFunctor::Id, BaseFunctor::Id) => ExtendedConstraint::default(),
            _ => panic!(),
        }
    }

    pub fn sub_prod_functor(&self, f: &ProdFunctor, g: &ProdFunctor) -> ExtendedConstraint {
        let mut res = ExtendedConstraint::default();
        assert_eq!(f.prod.len(), g.prod.len());
        for (x, y) in zip(&f.prod, &g.prod) {
            res = res & self.sub_base_functor(x, y)
        }
        res
    }

    // `p` is ground, solves all "value determined" indices in `q`
    // `p` must also be position independent
    pub fn sub_pos_typ(&self, p: &PosTyp, q: &PosTyp) -> ExtendedConstraint {
        match (p, q) {
            (PosTyp::Prod(p), PosTyp::Prod(q)) => {
                let iter = zip(p, q).map(|(p, q)| self.sub_pos_typ(p, q));
                constraint::and(iter)
            }
            (p, PosTyp::Refined(q, phi)) => {
                let w = self.sub_pos_typ(p, q);
                w.and_prop(phi)
            }
            (p, PosTyp::Exists(q)) => {
                let (this, evar) = self.new_evar(&q.tau);
                let q = (q.fun)(&evar);
                let w = this.sub_pos_typ(p, &q);
                w.push_down(&evar)
            }
            (PosTyp::Thunk(n), PosTyp::Thunk(m)) => {
                let (m, theta) = self.extract_neg(m);
                let w = Rc::new(Constraint::SubNegTyp(n.clone(), m));
                w.extend(&theta)
            }
            (PosTyp::Measured(f_alpha, t), PosTyp::Measured(g_alpha, t_)) => {
                assert_eq!(f_alpha.len(), g_alpha.len());
                let iter = zip(f_alpha, g_alpha).map(|(f_alpha, g_alpha)| {
                    assert!(f_alpha.1 == g_alpha.1);
                    self.sub_prod_functor(&f_alpha.0, &g_alpha.0)
                });
                let w = constraint::and(iter);
                w.inst(t, t_)
            }
            _ => panic!(),
        }
    }

    // `m` must be position independent
    // value determined instances in `n` are resolved
    pub fn sub_neg_type(&self, n: &NegTyp, m: &NegTyp) -> ExtendedConstraint {
        match (n, m) {
            (NegTyp::Force(p), NegTyp::Force(q)) => {
                let (p, theta) = self.extract_pos(p);
                let w = Rc::new(Constraint::SubPosTyp(p, q.clone()));
                w.extend(&theta)
            }
            (NegTyp::Implies(phi, n), m) => {
                let w = self.sub_neg_type(n, m);
                w.and_prop(phi)
            }
            (NegTyp::Forall(n), m) => {
                let (this, evar) = self.new_evar(&n.tau);
                let n = (n.fun)(&evar);
                let w = this.sub_neg_type(&n, m);
                w.push_down(&evar)
            }
            (NegTyp::Fun(p, n), NegTyp::Fun(q, m)) => {
                // arguments are swapped! (fun is contravariant in the argument)
                let w1 = self.sub_pos_typ(q, p);
                let w2 = self.sub_neg_type(n, m);
                w1 & w2
            }
            _ => panic!(),
        }
    }
}

impl Constraint {
    pub fn extend(mut self: Rc<Self>, theta: &[ContextPart]) -> ExtendedConstraint {
        for part in theta.iter().rev() {
            self = Rc::new(Self::Context(part.clone(), self));
        }
        ExtendedConstraint {
            w: self,
            r: Vec::new(),
        }
    }
}
