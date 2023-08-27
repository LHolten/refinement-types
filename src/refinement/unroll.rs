use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, PosTyp, Prop, Term};

impl SubContext {
    pub fn unroll_prod_univ(&self, term: &Rc<Term>, obj: &[Fun<PosTyp>], i: usize) -> Fun<PosTyp> {
        let g_beta = obj[i].clone();
        let term = term.clone();
        Fun {
            tau: g_beta.tau,
            fun: Rc::new(move |args| {
                let beta = Rc::new(Term::Inj(i, args.to_owned()));
                let mut g = (g_beta.fun)(args);
                g.prop.push(Prop::Eq(term.clone(), beta));
                g
            }),
        }
    }
}
