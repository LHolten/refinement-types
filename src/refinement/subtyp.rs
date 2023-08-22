use std::{iter::zip, rc::Rc};

use crate::refinement::{Context, SubContext};

use super::{
    Constraint, ContextPart, ExtendedConstraint, Fun, Measured, NegTyp, PosTyp, Prop, SolvedFun,
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
    pub fn extract<T>(mut self, n: &Fun<T>) -> (SolvedFun<T>, Vec<ContextPart>) {
        let mut args = vec![];
        let mut theta = vec![];
        for obj in &n.measured {
            let (this, uvar) = self.new_uvar(&obj.tau);
            self = this;
            args.push(uvar);
            theta.push(ContextPart::Free);
        }
        let (n, props) = (n.fun)(&args);
        for phi in props {
            theta.push(ContextPart::Assume(phi))
        }
        (n, theta)
    }

    pub fn extract_evar<T>(mut self, n: &Fun<T>) -> (SolvedFun<T>, Vec<Rc<Prop>>) {
        let mut args = vec![];
        let mut measured = vec![];
        for obj in &n.measured {
            let (this, evar) = self.new_evar(&obj.tau);
            self = this;
            args.push(evar.clone());
            measured.push((obj.clone(), evar));
        }
        let (inner, props) = (n.fun)(&args);
        let solve = SolvedFun { measured, inner };
        (solve, props)
    }

    // This should just compare by name
    pub fn eq_functor(&self, f: &Measured, g: &Measured) -> ExtendedConstraint {
        todo!()
    }

    // `p` is ground, solves all "value determined" indices in `q`
    // `p` must also be position independent
    // TODO: refactor these so that they do not use `self`
    // TODO: the evar do not need an index
    pub fn sub_pos_typ(mut self, p: &SolvedFun<PosTyp>, q: &Fun<PosTyp>) -> ExtendedConstraint {
        let (q, props) = self.extract_evar(q);

        let mut w = ExtendedConstraint::default();
        assert_eq!(p.measured.len(), q.measured.len());
        for ((p_obj, p_val), (q_obj, q_val)) in zip(&p.measured, &q.measured) {
            // TODO: instantiate q_val to p_val
            w = w & self.eq_functor(p_obj, q_obj);
        }

        assert_eq!(p.inner.thunks.len(), q.inner.thunks.len());
        for (n, m) in zip(&p.inner.thunks, &q.inner.thunks) {
            let (m_arg, theta) = self.extract(m);
            w = w & Rc::new(Constraint::SubNegTyp(n.clone(), m_arg)).extend(&theta);
        }

        for prop in props {
            w = w.and_prop(&prop);
        }
        w
    }

    // `m` must be position independent
    // value determined instances in `n` are resolved
    pub fn sub_neg_type(mut self, n: &Fun<NegTyp>, m: &SolvedFun<NegTyp>) -> ExtendedConstraint {
        let (n, props) = self.extract_evar(n);

        let mut w = ExtendedConstraint::default();
        assert_eq!(n.measured.len(), m.measured.len());
        // swapped m and n here, because args are contravariant
        for ((p_obj, p_val), (q_obj, q_val)) in zip(&m.measured, &n.measured) {
            // TODO: instantiate q_val to p_val
            w = w & self.eq_functor(p_obj, q_obj);
        }

        assert_eq!(n.inner.arg.thunks.len(), m.inner.arg.thunks.len());
        for (n_arg, m_arg) in zip(&n.inner.arg.thunks, &m.inner.arg.thunks) {
            let (m_arg, theta) = self.extract(m_arg);
            w = w & Rc::new(Constraint::SubNegTyp(n_arg.clone(), m_arg)).extend(&theta);
        }
        let (p, theta) = self.extract(&n.inner.ret);
        w = w & Rc::new(Constraint::SubPosTyp(p, m.inner.ret.clone())).extend(&theta);

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
