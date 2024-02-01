use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::refinement::SubContext;

use super::{heap::ConsumeErr, term::Term, Fun, InnerDiagnostic, NegTyp, PosTyp, Solved};

impl SubContext {
    pub fn extract<T>(&mut self, n: &Fun<T>) -> Solved<T> {
        let mut terms = vec![];
        for (tau, prefix) in &n.tau {
            let term = Term::fresh(prefix, *tau);
            terms.push(term);
        }

        let typ = self.append(|heap| {
            // TODO: check what happens when there is a conflict
            (n.fun)(heap, &terms).unwrap()
        });

        Solved { inner: typ, terms }
    }

    pub fn with_terms<T>(&mut self, typ: &Fun<T>, terms: &[Term]) -> Result<T, ConsumeErr> {
        let res = self.remove(|heap| {
            // TODO: check what happens when there is a conflict
            (typ.fun)(heap, terms).unwrap()
        });

        Ok(res)
    }

    pub fn sub_pos_typ(mut self, q: &Fun<PosTyp>, p: &Fun<PosTyp>) -> Result<(), SubTypErr> {
        let solved = self.extract(q);
        let PosTyp = self.with_terms(p, &solved.terms).using(q, p)?;
        self.check_empty().using(q, p)?;
        Ok(())
    }

    pub fn sub_neg_type(mut self, n: &Fun<NegTyp>, m: &Fun<NegTyp>) -> Result<(), SubTypErr> {
        let solved = self.extract(m);
        let typ = self.with_terms(n, &solved.terms).using(n, m)?;

        self.sub_pos_typ(&typ.ret, &solved.ret)
    }
}

trait IntoPosErr<T> {
    fn using<X>(self, have: &Fun<X>, need: &Fun<X>) -> Result<T, SubTypErr>;
}

impl<T, E> IntoPosErr<T> for Result<T, E>
where
    E: Diagnostic + Send + Sync + 'static,
{
    fn using<X>(self, have: &Fun<X>, need: &Fun<X>) -> Result<T, SubTypErr> {
        self.map_err(|err| SubTypErr {
            have: have.span,
            need: need.span,
            err: InnerDiagnostic::new(err),
        })
    }
}

#[derive(Error, Diagnostic, Debug)]
#[error("Not a subtype")]
pub struct SubTypErr {
    #[label]
    have: Option<SourceSpan>,
    #[label]
    need: Option<SourceSpan>,
    #[related]
    err: InnerDiagnostic,
}
