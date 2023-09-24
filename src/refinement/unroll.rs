use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, PosTyp, Term};

impl SubContext {
    pub fn unroll_prod_univ(&self, term: &Rc<Term>, i: usize) -> Fun<PosTyp> {
        let term = term.clone();
        Fun {
            tau: vec![], // no arguments
            fun: Rc::new(move |_terms, heap| {
                let beta = Rc::new(Term::Nat(i));
                heap.assert_eq(&term, &beta);
                PosTyp {
                    thunks: vec![], // no thunks
                }
            }),
        }
    }
}
