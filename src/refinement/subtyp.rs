use std::rc::Rc;

use crate::refinement::{typing::zip_eq, Context, SubContext};

use super::{Fun, InnerTerm, ListProp, Measured, NegTyp, PosTyp, Prop, Unsolved};

impl SubContext {
    // can we make this position independent into position independent??
    pub fn extract<T: ListProp>(&self, n: &Fun<T>) -> (T, Self) {
        let mut this = self.clone();
        let mut args = vec![];
        for tau in &n.tau {
            args.push(InnerTerm::UVar(this.univ, *tau).share());
            this.univ += 1;
        }
        let inner = (n.fun)(&args);
        for phi in inner.props() {
            let next = this.assume;
            this.assume = Rc::new(Context::Assume {
                phi: phi.clone(),
                next,
            });
        }
        (inner, this)
    }

    pub fn extract_evar<T: ListProp>(&self, n: &Fun<T>) -> (Unsolved<T>, Vec<Prop>) {
        let mut exis = self.exis;
        let mut args = vec![];
        for tau in &n.tau {
            args.push(InnerTerm::EVar(exis, *tau).share());
            exis += 1;
        }
        let inner = (n.fun)(&args);
        let props = inner.props().to_owned();
        let n = Unsolved { args, inner };
        (n, props)
    }

    // This is conservative and checks equality
    // solves evar in g
    pub fn eq_functor(&self, f: &Measured, g: &Measured) {
        // assert_eq!(f.f_alpha, g.f_alpha);
        // TODO: check equal inductive types by name
        g.term.instantiate(&f.term);
    }

    // `p` is ground, solves all "value determined" indices in `q`
    // `p` must also be position independent
    // TODO: refactor these so that they do not use `self`
    // TODO: the evar do not need an index
    pub fn sub_pos_typ(&self, p: &PosTyp, q: &Fun<PosTyp>) {
        let (q, props) = self.extract_evar(q);

        for (p_obj, q_obj) in zip_eq(&p.measured, &q.inner.measured) {
            self.eq_functor(p_obj, q_obj);
        }
        q.assert_resolved();
        self.verify_props(props);

        for (n, m) in zip_eq(&p.thunks, &q.inner.thunks) {
            let (m, this) = self.extract(m);
            this.sub_neg_type(n, &m);
        }
    }

    // `m` must be position independent
    // value determined instances in `n` are resolved
    pub fn sub_neg_type(&self, n: &Fun<NegTyp>, m: &NegTyp) {
        let (n, props) = self.extract_evar(n);

        // swapped m and n here, because args are contravariant
        for (p_obj, q_obj) in zip_eq(&m.arg.measured, &n.inner.arg.measured) {
            self.eq_functor(p_obj, q_obj);
        }
        n.assert_resolved();
        self.verify_props(props);

        for (n_arg, m_arg) in zip_eq(&n.inner.arg.thunks, &m.arg.thunks) {
            let (m_arg, this) = self.extract(m_arg);
            this.sub_neg_type(n_arg, &m_arg);
        }
        let (p, this) = self.extract(&n.inner.ret);
        this.sub_pos_typ(&p, &m.ret);
    }
}
