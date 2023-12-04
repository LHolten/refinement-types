use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, PosTyp, Term};

impl SubContext {
    pub fn unroll_prod_univ(&self, phi: Term) -> Fun<PosTyp> {
        Fun {
            tau: vec![], // no arguments
            fun: Rc::new(move |heap, _terms, ()| {
                heap.assert(phi.clone(), None)?;
                Ok(PosTyp::default())
            }),
            span: None,
        }
    }
}
