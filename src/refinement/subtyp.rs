use std::{iter::zip, rc::Rc};

use super::{
    BaseFunctor, Constraint, Context, NegTyp, PosTyp, ProdFunctor, Prop, Sort, SumFunctor, Term,
};

impl PosTyp {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl NegTyp {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl Constraint {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl Prop {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl Term {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl ProdFunctor {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl BaseFunctor {
    pub fn apply(&self, ctx: &Context) -> Rc<Self> {
        todo!()
    }
}

impl Context<'_> {
    pub fn inst(&self, phi: &Prop) {
        todo!()
    }

    pub fn inst_eq(&self, phi: &Prop, gamma: &Prop) {
        todo!()
    }

    pub fn exists(&self, tau: &Sort) -> Self {
        todo!()
    }

    pub fn forall(&self, tau: &Sort) -> Self {
        todo!()
    }

    pub fn index(&self, var: usize) -> &Option<Rc<Term>> {
        todo!()
    }

    pub fn extract_neg(&self, n: &NegTyp, m: &NegTyp) -> Rc<Constraint> {
        todo!()
    }

    pub fn extract_pos(&self, p: &PosTyp, q: &PosTyp) -> Rc<Constraint> {
        todo!()
    }

    pub fn equal_base_functor(&self, f: &BaseFunctor, g: &BaseFunctor) -> Rc<Constraint> {
        match (f, g) {
            (BaseFunctor::Pos(p), BaseFunctor::Pos(q)) => self.equal_pos_typ(p, q),
            (BaseFunctor::Id, BaseFunctor::Id) => Rc::new(Constraint::True),
            _ => panic!(),
        }
    }

    pub fn equal_prod_functor(&self, f: &ProdFunctor, g: &ProdFunctor) -> Rc<Constraint> {
        let mut res = Constraint::True;
        assert_eq!(f.prod.len(), g.prod.len());
        for (x, y) in zip(&f.prod, &g.prod) {
            let w = self.equal_base_functor(x, &y.apply(self));
            res = Constraint::And(res.apply(self), w);
        }
        Rc::new(res)
    }

    pub fn equal_functor(&self, f: &SumFunctor, g: &SumFunctor) -> Rc<Constraint> {
        let mut res = Constraint::True;
        assert_eq!(f.sum.len(), g.sum.len());
        for (x, y) in zip(&f.sum, &g.sum) {
            let w = self.equal_prod_functor(x, &y.apply(self));
            res = Constraint::And(res.apply(self), w);
        }
        Rc::new(res)
    }

    pub fn equal_pos_typ(&self, p: &PosTyp, q: &PosTyp) -> Rc<Constraint> {
        let res = match (p, q) {
            (PosTyp::Prod(p1, p2), PosTyp::Prod(q1, q2)) => {
                let w1 = self.equal_pos_typ(p1, q1);
                let w2 = self.equal_pos_typ(p2, &q2.apply(self));
                Constraint::And(w1.apply(self), w2)
            }
            (PosTyp::Sum(p1, p2), PosTyp::Sum(q1, q2)) => {
                let w1 = self.equal_pos_typ(p1, q1);
                let w2 = self.equal_pos_typ(p2, &q2.apply(self));
                Constraint::And(w1.apply(self), w2)
            }
            (PosTyp::Refined(p, phi), PosTyp::Refined(q, psi)) => {
                let w = self.equal_pos_typ(p, q);
                self.inst_eq(phi, &psi.apply(self));
                Constraint::And(
                    w.apply(self),
                    Rc::new(Constraint::PropEq(phi.clone(), psi.apply(self))),
                )
            }
            (PosTyp::Exists(tau, p), PosTyp::Exists(tau_, q)) => {
                assert_eq!(tau, tau_);
                let w = self.forall(tau).equal_pos_typ(p, q);
                Constraint::Forall(*tau, w)
            }
            (PosTyp::Thunk(n), PosTyp::Thunk(m)) => Constraint::EqNegTyp(n.clone(), m.clone()),
            (PosTyp::Measured(f, alpha, t), PosTyp::Measured(g, alpha_, t_)) => {
                assert!(alpha == alpha_);
                todo!()
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
                let w2 = self.sub_pos_typ(p2, &q2.apply(self));
                Constraint::And(w1.apply(self), w2)
            }
            (PosTyp::Sum(p1, p2), PosTyp::Sum(q1, q2)) => {
                let w1 = self.equal_pos_typ(p1, q1);
                let w2 = self.equal_pos_typ(p2, &q2.apply(self));
                Constraint::And(w1.apply(self), w2)
            }
            (p, PosTyp::Refined(q, phi)) => {
                let w = self.sub_pos_typ(p, q);
                self.inst(&phi.apply(self));
                Constraint::And(w.apply(self), Rc::new(Constraint::Prop(phi.apply(self))))
            }
            (p, PosTyp::Exists(tau, q)) => {
                let extended = self.exists(tau);
                let w = extended.sub_pos_typ(p, q);
                assert!(extended.index(0).is_some());
                return w;
            }
            (PosTyp::Thunk(n), PosTyp::Thunk(m)) => return self.extract_neg(n, m),
            (PosTyp::Measured(f, alpha, t), PosTyp::Measured(g, alpha_, t_)) => {
                // wtf is going on????
                assert!(alpha == alpha_);
                let mut w = self.equal_functor(f, g);
                let c = if let Term::Var(a) = t_.as_ref() {
                    // TODO: check that this is an existential
                    if let Some(t_) = self.index(*a) {
                        Constraint::Prop(Rc::new(Prop::Eq(t.clone(), t_.clone())))
                    } else {
                        self.inst(&Prop::Eq(t_.clone(), t.clone()));
                        w = w.apply(self);
                        // TODO: check that `t` is ground
                        Constraint::Prop(Rc::new(Prop::Eq(t.clone(), t.clone())))
                    }
                } else {
                    Constraint::Prop(Rc::new(Prop::Eq(t.clone(), t_.apply(self))))
                };
                Constraint::And(w, Rc::new(c))
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
                Constraint::And(w, Rc::new(Constraint::PropEq(psi.apply(self), phi.clone())))
            }
            (NegTyp::Forall(tau, n), NegTyp::Forall(tau_, m)) => {
                assert_eq!(tau, tau_);
                let w = self.equal_neg_type(n, m);
                Constraint::Forall(*tau, w)
            }
            (NegTyp::Fun(p, n), NegTyp::Fun(q, m)) => {
                let w1 = self.equal_pos_typ(p, q);
                let w2 = self.equal_neg_type(&n.apply(self), m);
                Constraint::And(w1.apply(self), w2)
            }
            _ => panic!(),
        };
        Rc::new(res)
    }

    // `m` is ground
    pub fn sub_neg_type(&self, n: &NegTyp, m: &NegTyp) -> Rc<Constraint> {
        let res = match (n, m) {
            (NegTyp::Force(p), NegTyp::Force(q)) => return self.extract_pos(p, q),
            (NegTyp::Implies(phi, n), m) => {
                let w = self.sub_neg_type(n, m);
                Constraint::And(w, Rc::new(Constraint::Prop(phi.apply(self))))
            }
            (NegTyp::Forall(tau, n), m) => {
                let extended = self.exists(tau);
                let w = extended.sub_neg_type(n, m);
                assert!(extended.index(0).is_some());
                return w;
            }
            (NegTyp::Fun(p, n), NegTyp::Fun(q, m)) => {
                let w1 = self.sub_pos_typ(q, p);
                let w2 = self.sub_neg_type(&n.apply(self), m);
                Constraint::And(w1.apply(self), w2)
            }
            _ => panic!(),
        };
        Rc::new(res)
    }
}
