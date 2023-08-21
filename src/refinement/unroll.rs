use std::rc::Rc;

use crate::refinement::{ExtendedConstraint, Prop, SubContext};

use super::{BaseFunctor, Fun, PosTyp, ProdFunctor, Term};

impl SubContext {
    // Solve variables while unrolling?
    pub fn unroll_prod(
        &self,
        f_alpha: &[(Rc<ProdFunctor>, Rc<Term>)],
        i: usize,
        t: &Rc<Term>,
    ) -> (Rc<PosTyp>, ExtendedConstraint) {
        let tau = self.infer_term(t);
        let (g, beta) = &f_alpha[i];
        let mut parts = vec![];
        for g in &g.prod {
            let res = match g {
                BaseFunctor::Pos(q) => q.clone(),
                BaseFunctor::Id => {
                    let f_alpha = f_alpha.to_owned();
                    let fun = Rc::new(move |idx: &Rc<Term>| {
                        Rc::new(PosTyp::Measured(f_alpha.clone(), idx.clone()))
                    });
                    Rc::new(PosTyp::Exists(Fun { tau, fun }))
                }
            };
            parts.push(res);
        }
        let cons = ExtendedConstraint::default().inst(beta, t);
        let res = Rc::new(PosTyp::Prod(parts));
        let prop = Rc::new(Prop::Eq(beta.clone(), t.clone()));
        (Rc::new(PosTyp::Refined(res, prop)), cons)
    }
}
