use crate::refinement::{
    heap::{HeapConsume, HeapProduce},
    SubContext,
};

use super::{Fun, NegTyp, PosTyp, Solved, Term};

impl SubContext {
    pub fn extract<T>(&mut self, n: &Fun<T>) -> Solved<T> {
        let mut terms = vec![];
        for tau in &n.tau {
            let term = Term::fresh("extract", *tau);
            terms.push(term);
        }

        let mut heap = HeapProduce(self);
        let typ = (n.fun)(&mut heap, &terms);

        Solved { inner: typ, terms }
    }

    pub fn with_terms<T>(&mut self, typ: &Fun<T>, terms: &[Term]) -> T {
        let mut heap = HeapConsume(self);

        assert_eq!(typ.tau.len(), terms.len());
        (typ.fun)(&mut heap, terms)
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
