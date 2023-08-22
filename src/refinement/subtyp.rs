use std::rc::Rc;

use crate::refinement::{typing::zip_eq, Context, SubContext};

use super::{
    Constraint, ContextPart, ExtendedConstraint, Fun, Measured, NegTyp, PosTyp, Prop, Unsolved,
};

impl SubContext {
    pub fn extend_univ(&self, theta: Vec<ContextPart>) -> Self {
        let mut next = self.assume.clone();
        let mut univ = self.univ;
        for part in theta {
            match part {
                ContextPart::Assume(phi) => next = Rc::new(Context::Assume { phi, next }),
                ContextPart::Free => univ += 1,
            }
        }
        Self {
            exis: self.exis,
            univ,
            assume: next,
        }
    }

    // can we make this position independent into position independent??
    pub fn extract<T>(mut self, n: &Fun<T>) -> (T, Vec<ContextPart>) {
        let mut args = vec![];
        let mut theta = vec![];
        for tau in &n.tau {
            let (this, uvar) = self.new_uvar(tau);
            self = this;
            args.push(uvar);
            theta.push(ContextPart::Free);
        }
        let (inner, props) = (n.fun)(&args);
        for phi in props {
            theta.push(ContextPart::Assume(phi))
        }
        (inner, theta)
    }

    pub fn extract_evar<T>(mut self, n: &Fun<T>) -> (Unsolved<T>, Vec<Rc<Prop>>) {
        let mut args = vec![];
        for tau in &n.tau {
            let (this, evar) = self.new_evar(&tau);
            self = this;
            args.push(evar.clone());
        }
        let (inner, props) = (n.fun)(&args);
        let n = Unsolved { args, inner };
        (n, props)
    }

    // This should just compare by name
    // TODO: solves evar in g
    pub fn eq_functor(&self, f: &Measured, g: &Measured) -> ExtendedConstraint {
        todo!()
    }

    // `p` is ground, solves all "value determined" indices in `q`
    // `p` must also be position independent
    // TODO: refactor these so that they do not use `self`
    // TODO: the evar do not need an index
    pub fn sub_pos_typ(mut self, p: &PosTyp, q: &Fun<PosTyp>) -> ExtendedConstraint {
        let (q, props) = self.extract_evar(q);

        let mut w = ExtendedConstraint::default();
        for (p_obj, q_obj) in zip_eq(&p.measured, &q.inner.measured) {
            w = w & self.eq_functor(p_obj, q_obj);
        }
        q.assert_resolved();

        for (n, m) in zip_eq(&p.thunks, &q.inner.thunks) {
            let (m, theta) = self.extract(m);
            w = w & self.extend_univ(theta).sub_neg_type(n, &m);
        }

        for prop in props {
            w = w.and_prop(&prop);
        }
        w
    }

    // `m` must be position independent
    // value determined instances in `n` are resolved
    pub fn sub_neg_type(mut self, n: &Fun<NegTyp>, m: &NegTyp) -> ExtendedConstraint {
        let (n, props) = self.extract_evar(n);

        let mut w = ExtendedConstraint::default();
        // swapped m and n here, because args are contravariant
        for (p_obj, q_obj) in zip_eq(&m.arg.measured, &n.inner.arg.measured) {
            w = w & self.eq_functor(p_obj, q_obj);
        }
        n.assert_resolved();

        for (n_arg, m_arg) in zip_eq(&n.inner.arg.thunks, &m.arg.thunks) {
            let (m_arg, theta) = self.extract(m_arg);
            w = w & self.extend_univ(theta).sub_neg_type(n_arg, &m_arg);
        }
        let (p, theta) = self.extract(&n.inner.ret);
        w = w & self.extend_univ(theta).sub_pos_typ(&p, &m.ret);

        for prop in props {
            w = w.and_prop(&prop);
        }
        w
    }
}

impl Constraint {
    pub fn extend(mut self: Rc<Self>, theta: &[ContextPart]) -> ExtendedConstraint {
        for part in theta.iter().rev() {
            self = Rc::new(Self::Context(part.clone(), self));
        }
        ExtendedConstraint {
            w: self,
            r: Vec::new(),
        }
    }
}
