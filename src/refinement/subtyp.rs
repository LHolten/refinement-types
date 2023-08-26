use std::rc::Rc;

use crate::refinement::{typing::zip_eq, Context, SubContext};

use super::{Fun, ListProp, NegTyp, PosTyp, Solved, Term};

impl SubContext {
    // can we make this position independent into position independent??
    pub fn extract<T: ListProp>(&self, n: &Fun<T>) -> (Solved<T>, Self) {
        let mut this = self.clone();
        let mut args = vec![];
        for tau in &n.tau {
            args.push(Rc::new(Term::UVar(this.univ, *tau)));
            this.univ += 1;
        }
        let solved = Solved {
            inner: (n.fun)(&args),
            args,
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

    // `p` is ground, solves all "value determined" indices in `q`
    // `p` must also be position independent
    // TODO: refactor these so that they do not use `self`
    // TODO: the evar do not need an index
    pub fn sub_pos_typ(&self, q: &Solved<PosTyp>, p: &Fun<PosTyp>) {
        let pos = (p.fun)(&q.args);
        self.verify_props(pos.prop);

        for (n, m) in zip_eq(&q.thunks, &pos.thunks) {
            let (m, this) = self.extract(m);
            this.sub_neg_type(n, &m);
        }
    }

    // `m` must be position independent
    // value determined instances in `n` are resolved
    pub fn sub_neg_type(&self, n: &Fun<NegTyp>, m: &Solved<NegTyp>) {
        let neg = (n.fun)(&m.args);
        self.verify_props(neg.arg.prop);

        for (n_arg, m_arg) in zip_eq(&neg.arg.thunks, &m.arg.thunks) {
            let (m_arg, this) = self.extract(m_arg);
            this.sub_neg_type(n_arg, &m_arg);
        }
        let (p, this) = self.extract(&neg.ret);
        this.sub_pos_typ(&p, &m.ret);
    }
}
