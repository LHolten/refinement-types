use std::{iter::zip, rc::Rc};

use super::{
    BaseFunctor, Constraint, Context, ContextPart, NegTyp, PosTyp, ProdFunctor, Prop, Sort,
    SumFunctor, Term,
};

impl Constraint {
    pub fn and(self: &Rc<Self>, rhs: Rc<Constraint>) -> Rc<Self> {
        Rc::new(Constraint::And(self.clone(), rhs))
    }

    pub fn and_prop(self: &Rc<Self>, rhs: &Rc<Prop>) -> Rc<Self> {
        Rc::new(Constraint::And(
            self.clone(),
            Rc::new(Constraint::Prop(rhs.clone())),
        ))
    }

    pub fn and_prop_eq(self: &Rc<Self>, lhs: &Rc<Prop>, rhs: &Rc<Prop>) -> Rc<Self> {
        Rc::new(Constraint::And(
            self.clone(),
            Rc::new(Constraint::PropEq(lhs.clone(), rhs.clone())),
        ))
    }
}

impl Context<'_> {
    // solve variables to grounded results
    // this needs to instantiate vars before checking if the result is grounded
    pub fn inst(&self, phi: &Prop) {
        todo!()
    }

    pub fn inst_eq(&self, phi: &Prop, psi: &Prop) {
        todo!()
    }

    pub fn exists(&self, tau: &Sort) -> Self {
        todo!()
    }

    pub fn forall(&self, tau: &Sort) -> Self {
        todo!()
    }

    pub fn get_exists(&self, var: usize) -> &Option<Rc<Term>> {
        todo!()
    }

    pub fn extract_neg(&self, n: &Rc<NegTyp>) -> (Rc<NegTyp>, Vec<ContextPart>) {
        match n.as_ref() {
            NegTyp::Implies(phi, n) => {
                let (n, mut theta) = self.extract_neg(n);
                theta.push(ContextPart::Assume(phi.clone()));
                (n, theta)
            }
            NegTyp::Forall(tau, n) => {
                let (n, mut theta) = self.forall(tau).extract_neg(n);
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
                let (p, mut theta) = self.forall(tau).extract_pos(p);
                theta.push(ContextPart::Free(*tau));
                (p, theta)
            }
            PosTyp::Prod(p1, p2) => {
                let (p1, mut theta1) = self.extract_pos(p1);
                let (p2, theta2) = self.extract_pos(p2);
                theta1.extend(theta2);
                (Rc::new(PosTyp::Prod(p1, p2)), theta1)
            }
            _ => (p.clone(), vec![]),
        }
    }

    pub fn equal_base_functor(&self, f: &BaseFunctor, g: &BaseFunctor) -> Rc<Constraint> {
        match (f, g) {
            (BaseFunctor::Pos(p), BaseFunctor::Pos(q)) => self.equal_pos_typ(p, q),
            (BaseFunctor::Id, BaseFunctor::Id) => Rc::new(Constraint::True),
            _ => panic!(),
        }
    }

    pub fn equal_prod_functor(&self, f: &ProdFunctor, g: &ProdFunctor) -> Rc<Constraint> {
        let mut res = Rc::new(Constraint::True);
        assert_eq!(f.prod.len(), g.prod.len());
        for (x, y) in zip(&f.prod, &g.prod) {
            let w = self.equal_base_functor(x, y);
            res = res.and(w);
        }
        res
    }

    pub fn equal_functor(&self, f: &SumFunctor, g: &SumFunctor) -> Rc<Constraint> {
        let mut res = Rc::new(Constraint::True);
        assert_eq!(f.sum.len(), g.sum.len());
        for (x, y) in zip(&f.sum, &g.sum) {
            let w = self.equal_prod_functor(x, y);
            res = res.and(w);
        }
        res
    }

    pub fn equal_pos_typ(&self, p: &PosTyp, q: &PosTyp) -> Rc<Constraint> {
        let res = match (p, q) {
            (PosTyp::Prod(p1, p2), PosTyp::Prod(q1, q2)) => {
                let w1 = self.equal_pos_typ(p1, q1);
                let w2 = self.equal_pos_typ(p2, q2);
                Constraint::And(w1, w2)
            }
            (PosTyp::Sum(p1, p2), PosTyp::Sum(q1, q2)) => {
                let w1 = self.equal_pos_typ(p1, q1);
                let w2 = self.equal_pos_typ(p2, q2);
                Constraint::And(w1, w2)
            }
            (PosTyp::Refined(p, phi), PosTyp::Refined(q, psi)) => {
                let w = self.equal_pos_typ(p, q);
                self.inst_eq(phi, psi);
                return w.and_prop_eq(phi, psi);
            }
            (PosTyp::Exists(tau, p), PosTyp::Exists(tau_, q)) => {
                assert_eq!(tau, tau_);
                let w = self.forall(tau).equal_pos_typ(p, q);
                Constraint::Forall(*tau, w)
            }
            (PosTyp::Thunk(n), PosTyp::Thunk(m)) => Constraint::EqNegTyp(n.clone(), m.clone()),
            (PosTyp::Measured(f, alpha, t), PosTyp::Measured(g, alpha_, t_)) => {
                assert!(alpha == alpha_);
                let w = self.equal_functor(f, g);
                let prop = Rc::new(Prop::Eq(t.clone(), t_.clone()));
                self.inst(&prop);
                return w.and_prop(&prop);
            }
            _ => panic!(),
        };
        Rc::new(res)
    }

    // `p` is ground
    pub fn sub_pos_typ(&self, p: &PosTyp, q: &PosTyp) -> Rc<Constraint> {
        let res = match (p, q) {
            (PosTyp::Prod(p1, p2), PosTyp::Prod(q1, q2)) => {
                let w1 = self.sub_pos_typ(p1, q1);
                let w2 = self.sub_pos_typ(p2, q2);
                Constraint::And(w1, w2)
            }
            (PosTyp::Sum(p1, p2), PosTyp::Sum(q1, q2)) => {
                let w1 = self.equal_pos_typ(p1, q1);
                let w2 = self.equal_pos_typ(p2, q2);
                Constraint::And(w1, w2)
            }
            (p, PosTyp::Refined(q, phi)) => {
                let w = self.sub_pos_typ(p, q);
                self.inst(phi);
                return w.and_prop(phi);
            }
            (p, PosTyp::Exists(tau, q)) => {
                let extended = self.exists(tau);
                let w = extended.sub_pos_typ(p, q);
                let Some(t) = extended.get_exists(0) else { panic!() };
                Constraint::Exists(*tau, t.clone(), w)
            }
            (PosTyp::Thunk(n), PosTyp::Thunk(m)) => {
                let (m, theta) = self.extract_neg(m);
                let w = Rc::new(Constraint::SubNegTyp(n.clone(), m));
                return w.extend(&theta);
            }
            (PosTyp::Measured(f, alpha, t), PosTyp::Measured(g, alpha_, t_)) => {
                assert!(alpha == alpha_);
                let w = self.equal_functor(f, g);
                let prop = Rc::new(Prop::Eq(t.clone(), t_.clone()));
                self.inst(&prop);
                return w.and_prop(&prop);
            }
            _ => panic!(),
        };
        Rc::new(res)
    }

    pub fn equal_neg_type(&self, n: &NegTyp, m: &NegTyp) -> Rc<Constraint> {
        let res = match (n, m) {
            (NegTyp::Force(p), NegTyp::Force(q)) => Constraint::EqPosTyp(p.clone(), q.clone()),
            (NegTyp::Implies(psi, n), NegTyp::Implies(phi, m)) => {
                let w = self.equal_neg_type(n, m);
                return w.and_prop_eq(psi, phi);
            }
            (NegTyp::Forall(tau, n), NegTyp::Forall(tau_, m)) => {
                assert_eq!(tau, tau_);
                let w = self.equal_neg_type(n, m);
                Constraint::Forall(*tau, w)
            }
            (NegTyp::Fun(p, n), NegTyp::Fun(q, m)) => {
                let w1 = self.equal_pos_typ(p, q);
                let w2 = self.equal_neg_type(n, m);
                Constraint::And(w1, w2)
            }
            _ => panic!(),
        };
        Rc::new(res)
    }

    // `m` is ground
    pub fn sub_neg_type(&self, n: &NegTyp, m: &NegTyp) -> Rc<Constraint> {
        let res = match (n, m) {
            (NegTyp::Force(p), NegTyp::Force(q)) => {
                let (p, theta) = self.extract_pos(p);
                let w = Rc::new(Constraint::SubPosTyp(p, q.clone()));
                return w.extend(&theta);
            }
            (NegTyp::Implies(phi, n), m) => {
                let w = self.sub_neg_type(n, m);
                return w.and_prop(phi);
            }
            (NegTyp::Forall(tau, n), m) => {
                let extended = self.exists(tau);
                let w = extended.sub_neg_type(n, m);
                let Some(t) = extended.get_exists(0) else { panic!() };
                Constraint::Exists(*tau, t.clone(), w)
            }
            (NegTyp::Fun(p, n), NegTyp::Fun(q, m)) => {
                // arguments are swapped! (fun is contravariant in the argument)
                let w1 = self.sub_pos_typ(q, p);
                let w2 = self.sub_neg_type(n, m);
                Constraint::And(w1, w2)
            }
            _ => panic!(),
        };
        Rc::new(res)
    }
}

impl Constraint {
    pub fn extend(mut self: Rc<Self>, theta: &[ContextPart]) -> Rc<Self> {
        for part in theta {
            let res = match part {
                ContextPart::Assume(phi) => Self::Implies(phi.clone(), self),
                ContextPart::Free(tau) => Self::Forall(*tau, self),
            };
            self = Rc::new(res)
        }
        self
    }
}
