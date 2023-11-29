use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::refinement::{
    heap::{HeapConsume, HeapProduce},
    SubContext,
};

use super::{typing::EmptyErr, Fun, NegTyp, PosTyp, Solved, Term};

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

    pub fn sub_pos_typ(mut self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) -> Result<(), PosErr> {
        let op = |err| PosErr {
            q: q.span,
            p: p.span,
            err,
        };

        let q = self.extract(q);
        let PosTyp = self.with_terms(p, &q.terms);
        self.check_empty().map_err(op)?;
        Ok(())
    }

    pub fn sub_neg_type(mut self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) -> Result<(), PosErr> {
        let m = self.extract(m);
        let typ = self.with_terms(n, &m.terms);

        self.sub_pos_typ(&typ.ret, &m.ret)
    }
}

#[derive(Error, Diagnostic, Debug)]
#[error("not a subtype")]
pub struct PosErr {
    #[label]
    q: Option<SourceSpan>,
    #[label]
    p: Option<SourceSpan>,
    err: EmptyErr,
}
