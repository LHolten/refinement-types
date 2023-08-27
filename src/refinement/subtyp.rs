use std::rc::Rc;

use crate::refinement::{typing::zip_eq, Context, SubContext};

use super::{Fun, ListProp, NegTyp, PosTyp, Solved, Term};

impl SubContext {
    pub fn extract<T: ListProp>(&self, n: &Fun<T>) -> (Solved<T>, Self) {
        let mut this = self.clone();
        let mut terms = vec![];
        for tau in &n.tau {
            terms.push(Rc::new(Term::UVar(this.univ, tau.clone())));
            this.univ += 1;
        }
        let solved = Solved {
            inner: (n.fun)(&terms),
            terms,
        };
        for phi in solved.props() {
            let next = this.assume;
            this.assume = Rc::new(Context::Assume {
                phi: phi.clone(),
                next,
            });
        }
        (solved, this)
    }

    pub fn sub_pos_typ(&self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) {
        let (q, this) = self.extract(q);
        let pos = (p.fun)(&q.terms);
        this.verify_props(pos.prop);

        for (n, m) in zip_eq(&q.thunks, &pos.thunks) {
            this.sub_neg_type(n, m);
        }
    }

    pub fn sub_neg_type(&self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) {
        let (m, this) = self.extract(m);
        let neg = (n.fun)(&m.terms);
        this.verify_props(neg.arg.prop);

        for (n_arg, m_arg) in zip_eq(&neg.arg.thunks, &m.arg.thunks) {
            this.sub_neg_type(n_arg, m_arg);
        }
        this.sub_pos_typ(&neg.ret, &m.ret);
    }
}
