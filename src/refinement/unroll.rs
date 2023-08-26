use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, Measured, PosTyp, Prop, Unsolved};

impl SubContext {
    // Solves outer variable with computation on new variables
    // returns PosTyp that contains new variables unsolved
    pub fn unroll_prod(&self, obj: &Measured, i: &usize) -> (Unsolved<PosTyp>, Vec<Prop>) {
        let g_beta = &obj.f_alpha[*i];
        let (g_beta, props) = self.extract_evar(g_beta);
        let (g, beta) = g_beta.inner;

        obj.term.instantiate(&beta);

        let solved = Unsolved {
            args: g_beta.args,
            inner: g,
        };
        (solved, props)
    }

    pub fn unroll_prod_univ(&self, obj: &Measured, i: &usize) -> Fun<PosTyp> {
        let g_beta = obj.f_alpha[*i].clone();
        let term = obj.term.clone();
        Fun {
            tau: g_beta.tau,
            fun: Rc::new(move |args| {
                let (mut g, beta) = (g_beta.fun)(args);
                g.prop.push(Prop::Eq(term.clone(), beta));
                g
            }),
        }
    }
}
