use std::{iter::zip, rc::Rc};

use crate::refinement::Prop;

use super::{
    Algebra, BaseFunctor, BasePattern, Context, PosTyp, ProdFunctor, ProdPattern, Sort, SumFunctor,
    Term,
};

struct Id {
    f: Rc<SumFunctor>,
    alpha: Rc<Algebra>,
    tau: Sort,
}

impl Context<'_> {
    pub fn unroll(self, id: &Id, t: &Rc<Term>) -> Rc<PosTyp> {
        let mut parts = vec![];
        assert_eq!(id.f.sum.len(), id.alpha.pats.len());
        for (g, beta) in zip(&id.f.sum, &id.alpha.pats) {
            parts.push(self.unroll_prod(id, g, beta, t))
        }
        // parts.into_iter().fol
        todo!()
    }

    // Solve variables while unrolling?
    pub fn unroll_prod(
        mut self,
        id: &Id,
        g: &ProdFunctor,
        beta: &(ProdPattern, Rc<Term>),
        t: &Rc<Term>,
    ) {
        let mut parts = vec![];
        assert_eq!(g.prod.len(), beta.0.parts.len());
        for (g, a) in zip(&g.prod, &beta.0.parts) {
            let res = match g {
                BaseFunctor::Pos(q) => q.clone(),
                BaseFunctor::Id => {
                    let BasePattern::Var(a) = a else { panic!() };
                    self = self.forall(&id.tau);
                    let m =
                        PosTyp::Measured(id.f.clone(), id.alpha.clone(), Rc::new(Term::Var(*a)));
                    Rc::new(PosTyp::Exists(id.tau, Rc::new(m)))
                }
            };
            parts.push(res);
        }
        let res = Rc::new(PosTyp::Prod(parts));
        let prop = Rc::new(Prop::Eq(t.clone(), beta.1.clone()));
        let _ = PosTyp::Refined(res, prop);
        // TODO: combine the parts into a list and then refine.
    }
}
