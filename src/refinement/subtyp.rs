use std::rc::Rc;

use crate::refinement::{typing::zip_eq, Context, SubContext};

use super::{Fun, NegTyp, PosTyp, Solved, Term, WithHeap};

impl SubContext {
    /// This also sets the heap in the new context
    pub fn extract<T>(&self, n: &Fun<T>) -> (Solved<T>, Self) {
        let mut this = self.clone();
        let mut terms = vec![];
        for tau in &n.tau {
            terms.push(Rc::new(Term::UVar(this.univ, *tau)));
            this.univ += 1;
        }
        let inner = n.with_terms(&terms);
        for phi in inner.heap.prop {
            let next = this.assume;
            this.assume = Rc::new(Context::Assume {
                phi: phi.clone(),
                next,
            });
        }
        // TODO: maybe we don't need `this.assume`, instead use `this.heap.prop`?
        this.heap.alloc.extend(inner.heap.alloc);
        let solved = Solved {
            inner: inner.typ,
            terms,
        };
        (solved, this)
    }

    pub fn sub_pos_typ(&self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) {
        let (q, this) = self.extract(q);
        let WithHeap { heap, typ } = p.with_terms(&q.terms);
        this.verify_props(heap);

        for (n, m) in zip_eq(&q.thunks, &typ.thunks) {
            this.sub_neg_type(n, m);
        }
    }

    pub fn sub_neg_type(&self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) {
        let (m, this) = self.extract(m);
        let WithHeap { heap, typ } = n.with_terms(&m.terms);
        this.verify_props(heap);

        for (n_arg, m_arg) in zip_eq(&typ.arg.thunks, &m.arg.thunks) {
            this.sub_neg_type(n_arg, m_arg);
        }
        this.sub_pos_typ(&typ.ret, &m.ret);
    }
}
