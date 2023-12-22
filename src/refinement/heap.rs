use std::mem::take;

use indenter::indented;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use super::{
    func_term::FuncTerm, term::Term, verify::format_model, CtxForall, Forall, Once, SubContext,
};

pub(super) struct HeapConsume<'a>(pub &'a mut SubContext);

impl<'a> std::ops::DerefMut for HeapConsume<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<'a> std::ops::Deref for HeapConsume<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

pub(super) struct HeapProduce<'a>(pub &'a mut SubContext);

impl<'a> std::ops::DerefMut for HeapProduce<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<'a> std::ops::Deref for HeapProduce<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

pub trait Heap {
    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr>;
    fn forall(&mut self, forall: Forall, value: Option<FuncTerm>) -> Result<FuncTerm, ConsumeErr>;
    fn once(&mut self, once: Once, value: Option<Term>) -> Result<Term, ConsumeErr> {
        let forall = Forall {
            named: once.named,
            mask: FuncTerm::exactly(&once.args),
            span: once.span,
        };
        let out = self.forall(forall, value.map(FuncTerm::always))?;
        Ok(out.apply(&once.args))
    }
}

impl Heap for HeapConsume<'_> {
    /// We can first look at aggregate resources of the correct name.
    /// After that we can iterate over the remaining resources one by one.
    fn forall(&mut self, need: Forall, value: Option<FuncTerm>) -> Result<FuncTerm, ConsumeErr> {
        match self.try_remove(need.clone()) {
            Ok(res) => {
                if let Some(value) = value {
                    self.masked_equal(&need, &value, &res);
                }
                Ok(res)
            }
            Err(need) => Err(ConsumeErr::MissingResource {
                resource: need.span,
                help: self.counter_example(need),
            }),
        }
    }

    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        if let Err(model) = self.verify_prop(&phi) {
            let mut out = String::new();
            format_model(indented(&mut out), model);
            return Err(ConsumeErr::InvalidAssert {
                assert: span,
                help: format!(
                    "Here is a valid example for which \n\
                    the assertion is false: \n{out}"
                ),
            });
        };
        Ok(())
    }
}

impl Heap for HeapProduce<'_> {
    /// Here we just put the aggregate to be used by consumption.
    fn forall(&mut self, forall: Forall, value: Option<FuncTerm>) -> Result<FuncTerm, ConsumeErr> {
        let value = value.unwrap_or_else(|| FuncTerm::free(&forall.named.arg_sizes()));
        self.forall.push(CtxForall {
            have: forall,
            value: value.clone(),
        });
        Ok(value)
    }

    fn assert(&mut self, phi: Term, _span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        self.assume.push(phi);
        Ok(())
    }
}

impl SubContext {
    // we make sure to return the minimal set of loans that is sufficient
    fn try_remove(&mut self, mut need: Forall) -> Result<FuncTerm, Forall> {
        struct Removal {
            mask: FuncTerm,
            value: FuncTerm,
        }

        fn build_value(removals: Vec<Removal>, last: Option<FuncTerm>) -> FuncTerm {
            let mut out = last.unwrap_or(FuncTerm::new(|_| Term::nat(0, 8)));
            for removal in removals.iter() {
                out = removal.mask.ite(&removal.value, &out);
            }
            out
        }

        let mut forall_list = take(&mut self.forall);
        let mut removals = vec![];

        // first we consume small allocations
        for alloc in forall_list.iter_mut() {
            if alloc.have.named.val_typ() != need.named.val_typ() {
                continue;
            }
            let overlap = Forall {
                named: need.named.clone(),
                mask: alloc.have.mask.and(&need.mask),
                span: None,
            };
            if !self.still_possible(&overlap) {
                continue;
            }
            let old_alloc_mask = alloc.have.mask.clone();
            alloc.have.mask = old_alloc_mask.difference(&need.mask);
            need.mask = need.mask.difference(&old_alloc_mask);
            removals.push(Removal {
                mask: old_alloc_mask,
                value: alloc.value.clone(),
            })
        }
        self.forall = forall_list;

        if self.still_possible(&need) {
            Err(need)
        } else {
            Ok(build_value(removals, None))
        }
    }
}

#[derive(Debug, Diagnostic, Error)]
pub enum ConsumeErr {
    #[error("Number of args is not equal")]
    NumArgs,

    #[error("The resource does not always exist")]
    MissingResource {
        #[label = "The resource"]
        resource: Option<SourceSpan>,
        #[help]
        help: String,
    },

    #[error("The assertion is not always true")]
    InvalidAssert {
        #[label = "The assertion"]
        assert: Option<SourceSpan>,
        #[help]
        help: String,
    },
}
