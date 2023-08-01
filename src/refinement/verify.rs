use std::rc::Rc;

use super::{Constraint, Context, Prop, TConstraint, Term};

impl<'a> Context<'a> {
    pub fn verify_prop(&self, phi: &Prop) {
        // This is where we need to use SMT
        todo!()
    }

    pub fn equal_prop(&self, phi: &Prop, psi: &Prop) {
        match (phi, psi) {
            (Prop::Eq(t1, t2), Prop::Eq(t1_, t2_)) => {
                self.verify_prop(&Prop::Eq(t1.clone(), t1_.clone()));
                self.verify_prop(&Prop::Eq(t2.clone(), t2_.clone()));
            }
        }
    }

    // Θ |= 𝑊
    pub fn verify(&self, w: &Constraint) {
        match w {
            Constraint::True => {}
            Constraint::And(w1, w2) => {
                self.verify(w1);
                self.verify(w2);
            }
            Constraint::Prop(phi) => self.verify_prop(phi),
            Constraint::PropEq(phi, psi) => self.equal_prop(phi, psi),
            Constraint::Forall(tau, w) => self.forall(tau).verify(w),
            Constraint::Implies(phi, w) => {
                todo!()
            }
            Constraint::Exists(tau, t, w) => {
                // TODO: remove this branch
                let extended = self.exists(tau);
                extended.inst(&Prop::Eq(Rc::new(Term::Var(0)), t.clone()));
                extended.verify(w);
            }
            Constraint::EqNegTyp(n, m) => {
                let w = self.equal_neg_type(n, m);
                self.verify(&w);
            }
            Constraint::EqPosTyp(p, q) => {
                let w = self.equal_pos_typ(p, q);
                self.verify(&w);
            }
            Constraint::SubNegTyp(n, m) => {
                let w = self.sub_neg_type(n, m);
                self.verify(&w);
            }
            Constraint::SubPosTyp(p, q) => {
                let w = self.sub_pos_typ(p, q);
                self.verify(&w);
            }
        }
    }

    pub fn verify_t(&self, xi: &TConstraint) {
        match xi {
            TConstraint::Cons(w) => self.verify(w),
            TConstraint::And(xi1, xi2) => {
                self.verify_t(xi1);
                self.verify_t(xi2);
            }
            TConstraint::Check(e, n) => {
                self.check_expr(e, n);
            }
        }
    }
}