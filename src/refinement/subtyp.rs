use std::{iter::zip, rc::Rc};

use crate::refinement::{constraint, Context, SubContext};

use super::{
    subst::Subst, BaseFunctor, Constraint, ContextPart, ExtendedConstraint, NegTyp, PosTyp,
    ProdFunctor, Sort, Term,
};

impl SubContext {
    pub fn add_exis(&self, tau: &Sort) -> Self {
        Self {
            exis: Rc::new(Context::Cons {
                part: ContextPart::Free(*tau),
                next: self.exis.clone(),
            }),
            univ: self.univ.clone(),
        }
    }

    pub fn add_univ(&self, tau: &Sort) -> Self {
        self.extend_univ(vec![ContextPart::Free(*tau)])
    }

    pub fn extend_univ(&self, theta: Vec<ContextPart>) -> Self {
        let mut next = self.univ.clone();
        for part in theta {
            next = Rc::new(Context::Cons { part, next })
        }
        Self {
            exis: self.exis.clone(),
            univ: next,
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
            NegTyp::Forall(tau, n) => {
                // we keep `n` positionally independent
                let gvar = Rc::new(Term::UVar(self.len(), *tau));
                let n = n.subst(Subst::Local(0), &gvar);
                let (n, mut theta) = self.add_univ(tau).extract_neg(&n);
                theta.push(ContextPart::Free(*tau));
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
            PosTyp::Exists(tau, p) => {
                let gvar = Rc::new(Term::UVar(self.len(), *tau));
                let p = p.subst(Subst::Local(0), &gvar);
                let (p, mut theta) = self.add_univ(tau).extract_pos(&p);
                theta.push(ContextPart::Free(*tau));
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
            (p, PosTyp::Exists(tau, q)) => {
                let evar = Rc::new(Term::EVar(self.len(), *tau));
                let q = q.subst(Subst::Local(0), &evar);
                let w = self.add_exis(tau).sub_pos_typ(p, &q);
                w.push_down(self.len())
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
                // `p` might have existential variables refering to our scope
                // we remove a bunch of binders and add them in the constraint
                // this keeps the existential variables correctly bound, because
                // we will add the existential variables to the the context when they are solved.
                // we do not update the variables that were bound by `theta`
                // Luckily all vars start out as LVar, so this is fine!
                let (p, theta) = self.extract_pos(p);
                let w = Rc::new(Constraint::SubPosTyp(p, q.clone()));
                w.extend(&theta)
            }
            (NegTyp::Implies(phi, n), m) => {
                let w = self.sub_neg_type(n, m);
                w.and_prop(phi)
            }
            (NegTyp::Forall(tau, n), m) => {
                let idx = self.len();
                let n = n.subst(Subst::Local(0), &Rc::new(Term::UVar(idx, *tau)));
                let w = self.add_exis(tau).sub_neg_type(&n, m);
                w.push_down(idx)
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
        for part in theta {
            let res = match part {
                ContextPart::Assume(phi) => Self::Implies(phi.clone(), self),
                ContextPart::Free(tau) => Self::Forall(*tau, self),
            };
            self = Rc::new(res)
        }
        ExtendedConstraint {
            w: self,
            r: Vec::new(),
        }
    }
}
