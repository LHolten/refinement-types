use std::rc::Rc;

use crate::refinement::{typing::zip_eq, Context, Resource, SubContext};

use super::{Fun, NegTyp, PosTyp, Solved, Term, WithProp};

impl SubContext {
    /// This also sets the heap in the new context
    pub fn extract<T>(&self, n: &Fun<T>) -> (Solved<T>, Self) {
        let mut this = self.clone();
        let mut terms = vec![];
        for tau in &n.tau {
            terms.push(Rc::new(Term::UVar(this.univ, *tau)));
            this.univ += 1;
        }
        let mut alloc = vec![];
        for spec in &n.alloc {
            alloc.push(Resource {
                ptr: spec.ptr.clone(),
                value: Rc::new(Term::UVar(this.univ, spec.tau)),
            });
            this.univ += 1;
        }
        this.alloc.extend(alloc.clone());

        let WithProp { prop, typ } = n.with_terms(&mut alloc, &terms);
        // make sure that it actually uses what it says
        assert!(alloc.is_empty());

        for phi in prop {
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

    pub fn sub_pos_typ(&self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) {
        let (q, mut this) = self.extract(q);
        let WithProp { prop, typ } = p.with_terms(&mut this.alloc, &q.terms);
        this.verify_props(&prop);

        for (n, m) in zip_eq(&q.thunks, &typ.thunks) {
            this.sub_neg_type(n, m);
        }
    }

    pub fn sub_neg_type(&self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) {
        let (m, mut this) = self.extract(m);
        let WithProp { prop, typ } = n.with_terms(&mut this.alloc, &m.terms);
        this.verify_props(&prop);

        for (n_arg, m_arg) in zip_eq(&typ.arg.thunks, &m.arg.thunks) {
            this.sub_neg_type(n_arg, m_arg);
        }
        this.sub_pos_typ(&typ.ret, &m.ret);
    }
}
