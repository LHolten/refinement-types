use std::rc::Rc;

use z3::ast::Int;

use crate::{
    refinement::{
        heap::{HeapConsume, HeapProduce},
        Sort, SubContext,
    },
    solver::ctx,
};

use super::{Fun, NegTyp, PosTyp, Solved, Term};

impl SubContext {
    pub fn extract<T>(&mut self, n: &Fun<T>) -> Solved<T> {
        let mut terms = vec![];
        for tau in &n.tau {
            assert_eq!(tau, &Sort::Nat);
            let term = Int::new_const(ctx(), self.univ);
            terms.push(Rc::new(Term::UVar(term, *tau)));
            self.univ += 1;
        }

        let mut heap = HeapProduce(self);
        let typ = (n.fun)(&terms, &mut heap);

        Solved { inner: typ, terms }
    }

    pub fn with_terms<T>(&mut self, typ: &Fun<T>, terms: &[Rc<Term>]) -> T {
        let mut heap = HeapConsume(self);

        assert_eq!(typ.tau.len(), terms.len());
        (typ.fun)(terms, &mut heap)
    }

    pub fn sub_pos_typ(mut self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) {
        let q = self.extract(q);
        let PosTyp = self.with_terms(p, &q.terms);
        self.check_empty()
    }

    pub fn sub_neg_type(mut self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) {
        let m = self.extract(m);
        let typ = self.with_terms(n, &m.terms);

        self.sub_pos_typ(&typ.ret, &m.ret);
    }
}
