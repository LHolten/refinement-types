use std::rc::Rc;

use crate::refinement::Prop;

use super::{BaseFunctor, Context, PosTyp, ProdFunctor, Sort, Term};

pub(super) struct Id {
    pub f_alpha: Vec<(Rc<ProdFunctor>, Rc<Term>)>,
    pub tau: Sort,
}

impl Context<'_> {
    // Solve variables while unrolling?
    pub fn unroll_prod(
        &self,
        id: &Id,
        g: &ProdFunctor,
        beta: &Rc<Term>,
        t: &Rc<Term>,
    ) -> Rc<PosTyp> {
        let mut parts = vec![];
        for g in &g.prod {
            let res = match g {
                BaseFunctor::Pos(q) => q.clone(),
                BaseFunctor::Id => {
                    let m = PosTyp::Measured(id.f_alpha.clone(), Rc::new(Term::Var(0)));
                    Rc::new(PosTyp::Exists(id.tau, Rc::new(m)))
                }
            };
            parts.push(res);
        }
        let res = Rc::new(PosTyp::Prod(parts));
        let prop = Rc::new(Prop::Eq(t.clone(), beta.clone()));
        Rc::new(PosTyp::Refined(res, prop))
    }
}
