use std::rc::Rc;

use crate::refinement::ContextPart;

use super::{Constraint, Context, Prop};

impl Context {
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
    pub fn verify(self: &Rc<Self>, w: &Constraint) {
        match w {
            Constraint::True => {}
            Constraint::And(w1, w2) => {
                self.verify(w1);
                self.verify(w2);
            }
            Constraint::Prop(phi) => self.verify_prop(phi),
            Constraint::PropEq(phi, psi) => self.equal_prop(phi, psi),
            Constraint::Forall(tau, w) => self.add(tau).verify(w),
            Constraint::Implies(phi, w) => {
                let extended = self.extend(vec![ContextPart::Assume(phi.clone())]);
                extended.verify(w);
            }
            Constraint::SubNegTyp(n, m) => {
                let w = self.sub_neg_type(n, m);
                self.verify(&w.w);
            }
            Constraint::SubPosTyp(p, q) => {
                let w = self.sub_pos_typ(p, q);
                self.verify(&w.w);
            }
            Constraint::Check(e, n) => {
                self.check_expr(e, n);
            }
        }
    }
}
