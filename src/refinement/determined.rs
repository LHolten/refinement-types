use std::{cmp::max, iter::zip, rc::Rc};

use crate::refinement::SubContext;

use super::{InnerTerm, Prop, Sort, Term};

pub fn or(mut r1: Vec<bool>, mut r2: Vec<bool>) -> Vec<bool> {
    let total_len = max(r1.len(), r2.len());
    r1.resize(total_len, false);
    r2.resize(total_len, false);
    zip(r1, r2).map(|(x, y)| x | y).collect()
}

impl SubContext {
    pub fn infer_prop(&self, phi: &Prop) -> Sort {
        match phi {
            Prop::Eq(a, b) => {
                assert_eq!(self.infer_term(a), self.infer_term(b));
            }
        }
        Sort::Bool
    }

    pub fn infer_term(&self, t: &Term) -> Sort {
        match *t.borrow() {
            InnerTerm::UVar(_, s) => s,
            InnerTerm::EVar(_, s) => s,
            InnerTerm::Prop(ref phi) => self.infer_prop(phi),
            InnerTerm::Zero => Sort::Nat,
        }
    }

    pub fn new_uvar(&self, tau: &Sort) -> (Self, Rc<Term>) {
        let uvar = InnerTerm::UVar(self.univ, *tau).share();
        let this = Self {
            exis: self.exis,
            univ: self.univ + 1,
            assume: self.assume.clone(),
        };
        (this, uvar)
    }

    pub fn new_evar(&self, tau: &Sort) -> (Self, Rc<Term>) {
        let evar = InnerTerm::EVar(self.exis, *tau).share();
        let this = Self {
            exis: self.exis + 1,
            univ: self.univ,
            assume: self.assume.clone(),
        };
        (this, evar)
    }
}
