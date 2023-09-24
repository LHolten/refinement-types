use std::{mem::take, rc::Rc};

use crate::refinement::{
    heap::{HeapConsume, HeapProduce},
    typing::zip_eq,
    Context, SubContext,
};

use super::{Fun, NegTyp, PosTyp, Solved, Term};

impl SubContext {
    /// This also sets the heap in the new context
    pub fn extract<T>(&self, n: &Fun<T>) -> (Solved<T>, Self) {
        let mut this = self.clone();
        let mut terms = vec![];
        for tau in &n.tau {
            terms.push(Rc::new(Term::UVar(this.univ, *tau)));
            this.univ += 1;
        }

        let mut heap = HeapProduce {
            univ: this.univ,
            alloc: take(&mut this.alloc),
            prop: vec![],
        };
        let typ = (n.fun)(&terms, &mut heap);
        this.alloc = heap.alloc;

        for phi in heap.prop {
            // self.solver.assert(ast)
            let next = this.assume;
            this.assume = Rc::new(Context::Assume {
                phi: phi.clone(),
                next,
            });
        }

        let solved = Solved { inner: typ, terms };
        (solved, this)
    }

    pub fn with_terms<T>(&mut self, typ: &Fun<T>, terms: &[Rc<Term>]) -> T {
        let mut heap = HeapConsume(self);

        assert_eq!(typ.tau.len(), terms.len());
        (typ.fun)(terms, &mut heap)
    }

    pub fn sub_pos_typ(&self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) {
        let (q, mut this) = self.extract(q);
        let typ = this.with_terms(p, &q.terms);

        for (n, m) in zip_eq(&q.thunks, &typ.thunks) {
            this.sub_neg_type(n, m);
        }
    }

    pub fn sub_neg_type(&self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) {
        let (m, mut this) = self.extract(m);
        let typ = this.with_terms(n, &m.terms);

        for (n_arg, m_arg) in zip_eq(&typ.arg.thunks, &m.arg.thunks) {
            this.sub_neg_type(n_arg, m_arg);
        }
        this.sub_pos_typ(&typ.ret, &m.ret);
    }
}
