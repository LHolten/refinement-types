use indenter::indented;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::ast::BV;

use crate::{refinement::Hint, solver::ctx};

use super::{
    func_term::FuncTerm, term::Term, verify::format_model, CtxForall, Forall, PosTyp, Resource,
    SubContext, Switch,
};

pub(super) struct HeapConsume<'a>(pub &'a mut SubContext, pub Vec<CtxForall>, pub Term);

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

pub(super) struct HeapProduce<'a>(pub &'a mut SubContext, pub Vec<CtxForall>);

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

pub struct ForallRes {
    // result of the unpacked resource
    pub removals: Vec<CtxForall>,
}

impl ForallRes {
    pub fn get_byte(&self, idx: &[Term]) -> Term {
        let mut val = BV::from_i64(ctx(), 0, 8);
        for removal in &self.removals {
            if let Resource::Owned = removal.have.resource {
                let cond = removal.have.mask.apply_bool(idx);
                let new = removal.value.apply(idx).to_bv();
                val = cond.ite(&new, &val);
            }
        }
        Term::BV(val)
    }
}

pub trait Heap {
    fn exactly(&mut self, forall: CtxForall) -> Result<(), ConsumeErr>;

    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr>;
    fn forall(&mut self, forall: Forall) -> Result<(), ConsumeErr>;
    fn once(&mut self, switch: Switch) -> Result<(), ConsumeErr>;

    #[allow(clippy::type_complexity)]
    fn apply(
        &mut self,
        f: Box<dyn FnOnce(&mut dyn Heap) -> Result<(), ConsumeErr>>,
    ) -> Result<ForallRes, ConsumeErr>;
}

impl Heap for HeapConsume<'_> {
    fn exactly(&mut self, forall: CtxForall) -> Result<(), ConsumeErr> {
        // TODO: need to modify mask?
        let got = self.try_remove(forall.have.clone())?;
        for removal in got.removals {
            self.assume
                .masked_equal(&removal.have, &removal.value, &forall.value);
        }
        self.1.push(forall);
        Ok(())
    }

    /// We can first look at aggregate resources of the correct name.
    /// After that we can iterate over the remaining resources one by one.
    fn forall(&mut self, mut need: Forall) -> Result<(), ConsumeErr> {
        need.mask = need.mask.and(&FuncTerm::always(self.2.clone()));

        let res = self.try_remove(need.clone())?;

        self.1.extend(res.removals);
        Ok(())
    }

    fn once(&mut self, switch: Switch) -> Result<(), ConsumeErr> {
        if let Resource::Named(named) = &switch.resource {
            self.hints.push(Hint {
                id: named.id,
                args: switch.args.clone(),
            });
        }

        let forall = Forall {
            resource: switch.resource.clone(),
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
            span: switch.span,
        };
        self.forall(forall)
    }

    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        let phi = self.2.implies(&phi);

        if let Err(model) = self.assume.verify_prop(&phi) {
            let mut out = String::new();
            format_model(indented(&mut out), model, self.scope.as_ref().unwrap());
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

    fn apply(
        &mut self,
        f: Box<dyn FnOnce(&mut dyn Heap) -> Result<(), ConsumeErr>>,
    ) -> Result<ForallRes, ConsumeErr> {
        let cond = self.2.clone();
        let mut heap = HeapConsume(self, vec![], cond);
        f(&mut heap)?;
        let new_forall = heap.1;
        self.1.extend(new_forall.clone());
        Ok(ForallRes {
            removals: new_forall,
        })
    }
}

impl Heap for HeapProduce<'_> {
    fn exactly(&mut self, forall: CtxForall) -> Result<(), ConsumeErr> {
        self.1.push(forall);
        Ok(())
    }

    /// Here we just put the aggregate to be used by consumption.
    fn forall(&mut self, have: Forall) -> Result<(), ConsumeErr> {
        let forall = CtxForall {
            value: FuncTerm::free(&have.resource.arg_sizes()),
            have,
        };
        self.1.push(forall);
        Ok(())
    }

    fn once(&mut self, switch: Switch) -> Result<(), ConsumeErr> {
        if let Resource::Named(named) = &switch.resource {
            self.hints.push(Hint {
                id: named.id,
                args: switch.args.clone(),
            });

            if self.assume.is_always_true(switch.cond.to_bool()) {
                (named.typ.fun)(self, &switch.args)?;
                return Ok(());
            };
        }

        let forall = Forall {
            resource: switch.resource.clone(),
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
            span: switch.span,
        };
        self.forall(forall)
    }

    fn assert(&mut self, phi: Term, _span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        self.assume.assumptions.push(phi);
        Ok(())
    }

    fn apply(
        &mut self,
        f: Box<dyn FnOnce(&mut dyn Heap) -> Result<(), ConsumeErr>>,
    ) -> Result<ForallRes, ConsumeErr> {
        let mut heap = HeapProduce(self, vec![]);
        f(&mut heap)?;
        let new_forall = heap.1;
        self.1.extend(new_forall.clone());
        Ok(ForallRes {
            removals: new_forall,
        })
    }
}

impl SubContext {
    // we make sure to return the minimal set of loans that is sufficient
    fn try_remove(&mut self, mut need: Forall) -> Result<ForallRes, ConsumeErr> {
        let mut removals = vec![];

        let mut allowed: Vec<_> = self
            .forall
            .iter_mut()
            .filter(|x| x.have.resource == need.resource)
            .collect();

        for i in 0..allowed.len() {
            let mut mask = allowed[i].have.mask.clone();
            let others = allowed[0..i].iter().chain(&allowed[i + 1..]);
            others.for_each(|item| {
                mask = mask.difference(&item.have.mask);
            });
            if !self.assume.still_possible(&Forall {
                resource: need.resource.clone(),
                mask,
                span: None,
            }) {
                continue;
            }
            let overlap = Forall {
                resource: need.resource.clone(),
                mask: allowed[i].have.mask.and(&need.mask),
                span: need.span,
            };
            let old_alloc_mask = allowed[i].have.mask.clone();
            allowed[i].have.mask = old_alloc_mask.difference(&need.mask);
            need.mask = need.mask.difference(&old_alloc_mask);
            removals.push(CtxForall {
                have: overlap,
                value: allowed[i].value.clone(),
            });
        }

        self.forall.retain(|x| self.assume.still_possible(&x.have));

        if let Resource::Named(named) = &need.resource {
            let hints = self.hints.clone();
            let hints = hints.into_iter().filter(|h| h.id == named.id);

            for hint in hints {
                let cond = need.mask.apply(&hint.args);
                if self.assume.is_always_true(cond.to_bool().not()) {
                    continue;
                }
                need.mask = need.mask.difference(&FuncTerm::exactly(&hint.args));

                let mut consume = HeapConsume(self, vec![], cond);
                let PosTyp = (named.typ.fun)(&mut consume, &hint.args)?;
                removals.extend(consume.1);
            }
        }

        if !self.assume.still_possible(&need) {
            return Ok(ForallRes { removals });
        }

        Err(ConsumeErr::MissingResource {
            resource: need.span,
            help: self
                .assume
                .counter_example(need, &self.forall, self.scope.as_ref().unwrap()),
        })
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
