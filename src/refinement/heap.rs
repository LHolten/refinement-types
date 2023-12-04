use std::mem::take;

use indenter::indented;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use super::{
    func_term::FuncTerm, term::Term, verify::format_model, Cond, CtxForall, Forall, Resource,
    SubContext,
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
    // load bytes and store in size bits
    fn owned(&mut self, ptr: &Term, bytes: u32, size: u32) -> Result<Term, ConsumeErr> {
        let mut res = self.owned_byte(ptr, None)?;
        let mut ptr = ptr.clone();
        for _ in 1..bytes {
            ptr = ptr.add(&Term::nat(1, 32));
            // little endian, so new value is more significant
            let val = self.owned_byte(&ptr, None)?;
            res = val.concat(&res);
        }
        Ok(res.extend_to(size))
    }
    fn owned_byte(&mut self, ptr: &Term, span: Option<SourceSpan>) -> Result<Term, ConsumeErr> {
        let value = self.forall(Forall {
            named: Resource::Owned,
            mask: FuncTerm::exactly(&[ptr.to_owned()]),
            span,
        })?;
        Ok(value.apply(&[ptr.to_owned()]))
    }
    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr>;
    fn forall(&mut self, forall: Forall) -> Result<FuncTerm, ConsumeErr>;
    fn switch(&mut self, cond: Cond) -> Result<(), ConsumeErr> {
        let condition = FuncTerm::new_bool(move |_| cond.cond.to_bool());
        self.forall(Forall {
            named: Resource::Named(cond.named),
            mask: FuncTerm::exactly(&cond.args).and(&condition),
            span: Some(cond.span),
        })?;
        Ok(())
    }
}

impl Heap for HeapConsume<'_> {
    fn switch(&mut self, cond: Cond) -> Result<(), ConsumeErr> {
        let condition = FuncTerm::new_bool(move |_| cond.cond.to_bool());
        let need = Forall {
            named: Resource::Named(cond.named.clone()),
            mask: FuncTerm::exactly(&cond.args).and(&condition),
            span: Some(cond.span),
        };

        if let Err(need) = self.try_remove(need) {
            let res = need.mask.apply_bool(&cond.args);
            if self.is_always_true(res) {
                // TODO: add a wrapper to make this clearer
                (cond.named.upgrade().unwrap().typ.fun)(self, &cond.args)?;
            } else {
                return Err(ConsumeErr::MissingResource {
                    resource: need.span,
                    help: self.counter_example(need),
                });
            }
        }
        Ok(())
    }

    /// We can first look at aggregate resources of the correct name.
    /// After that we can iterate over the remaining resources one by one.
    fn forall(&mut self, need: Forall) -> Result<FuncTerm, ConsumeErr> {
        match self.try_remove(need) {
            Ok(res) => Ok(res),
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
    fn forall(&mut self, forall: Forall) -> Result<FuncTerm, ConsumeErr> {
        let value = FuncTerm::free(&forall.arg_sizes());
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
            if alloc.have.id() != need.id() {
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
