use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, PosTyp, Term};

impl SubContext {
    pub fn unroll_prod_univ(&self, phi: Term) -> Fun<PosTyp> {
        Fun {
            tau: vec![], // no arguments
            fun: Rc::new(move |_terms, heap| {
                heap.assert(phi.clone());
                PosTyp {}
            }),
        }
    }
}
