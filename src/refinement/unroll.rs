use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, Measured, PosTyp, Prop, Term};

impl SubContext {
    pub fn unroll_prod_univ(&self, term: &Rc<Term>, obj: &Measured, i: &usize) -> Fun<PosTyp> {
        let g_beta = obj.f_alpha[*i].clone();
        let term = term.clone();
        Fun {
            tau: g_beta.tau,
            measured: g_beta.measured,
            fun: Rc::new(move |args| {
                let (mut g, beta) = (g_beta.fun)(args);
                g.prop.push(Prop::Eq(term.clone(), beta));
                g
            }),
        }
    }
}
