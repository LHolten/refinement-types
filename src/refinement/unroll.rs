use std::rc::Rc;

use crate::refinement::SubContext;

use super::{ContextPart, Measured, PosTyp, Prop, Unsolved};

impl SubContext {
    // Solves outer variable with computation on new variables
    // returns PosTyp that contains new variables unsolved
    pub fn unroll_prod(&self, obj: &Measured, i: &usize) -> (Unsolved<PosTyp>, Vec<Rc<Prop>>) {
        let tau = self.infer_term(&obj.term);
        let g_beta = &obj.f_alpha[*i];
        let (g_beta, props) = self.extract_evar(g_beta);
        let (mut g, beta) = g_beta.inner;

        obj.term.instantiate(&beta);

        let inner = PosTyp {
            measured: g.measured,
            thunks: g.thunks,
        };
        let solved = Unsolved {
            args: g_beta.args,
            inner,
        };
        (solved, props)
    }

    pub fn unroll_prod_univ(&self, obj: &Measured, i: &usize) -> (PosTyp, Vec<ContextPart>) {
        let tau = self.infer_term(&obj.term);
        let g_beta = &obj.f_alpha[*i];
        let (g_beta, theta) = self.extract(g_beta);
        let (mut g, beta) = g_beta;

        obj.term.instantiate(&beta);
        // let eq = Rc::new(Prop::Eq(obj.term, beta));
        // theta.push(ContextPart::Assume(eq));

        let inner = PosTyp {
            measured: g.measured,
            thunks: g.thunks,
        };
        (inner, theta)
    }
}
