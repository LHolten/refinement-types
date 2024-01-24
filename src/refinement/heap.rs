use std::collections::HashMap;

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::ast::BV;

use crate::solver::ctx;

use super::{func_term::FuncTerm, term::Term, CtxForall, Forall, Resource, SubContext, Switch};

// keeps track of a linear resource that is in scope
#[derive(Clone)]
pub struct NewPart {
    pub resource: Resource,
    unpacked: Vec<Unpacked>,
    pub mask: FuncTerm,
    value: FuncTerm,
}

// keeps track of a resource that has been partially used
#[derive(Clone)]
pub struct Unpacked {
    terms: Vec<Term>,
    parts: HashMap<String, NewPart>,
}

pub(super) struct HeapConsume<'a> {
    pub inner: &'a mut SubContext,
    // pub new_scope: HashMap<String, NewPart>,
    pub translate: HashMap<String, Translate>,
}

#[derive(Clone)]
pub enum Translate {
    Just(Proj),
    Construct(HashMap<String, Translate>),
}

impl Translate {
    pub fn simple(name: String) -> Self {
        Self::Just(Proj {
            parts: vec![],
            last: name,
        })
    }
}

#[derive(Clone)]
pub struct Proj {
    parts: Vec<(String, Vec<Term>)>,
    last: String,
}

impl<'a> std::ops::DerefMut for HeapConsume<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'a> std::ops::Deref for HeapConsume<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

pub(super) struct HeapProduce<'a> {
    pub inner: &'a mut SubContext,
    // the value of the resource we are expanding inside
    pub scope_value: Term,
    pub new_scope: HashMap<String, NewPart>,
}

impl<'a> std::ops::DerefMut for HeapProduce<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'a> std::ops::Deref for HeapProduce<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.inner
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
    fn forall(&mut self, forall: Forall) -> Result<FuncTerm, ConsumeErr>;
    fn once(&mut self, switch: Switch) -> Result<Term, ConsumeErr>;

    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        let switch = Switch {
            resource: Resource::Impossible,
            args: vec![],
            cond: phi.bool_not(),
            name: "_".to_owned(),
            span,
        };

        self.once(switch)?;
        Ok(())
    }
}

impl Heap for HeapConsume<'_> {
    fn forall(&mut self, mut need: Forall) -> Result<FuncTerm, ConsumeErr> {
        // TODO: skip everything if cond is impossible
        let trans = &self.translate[&need.name];
        let Translate::Just(proj) = trans else {
            panic!("can not construct forall")
        };

        let have = self.try_remove(proj)?;
        // check that the resource type is correct
        assert!(need.resource == have.resource);

        // check that we have all the indices
        let idx = need.resource.make_fresh_args();
        let cond = need
            .mask
            .apply_bool(&idx)
            .implies(&have.mask.apply_bool(&idx));
        assert!(self.assume.is_always_true(cond), "missing a resource");

        // remove the resources
        have.mask = have.mask.difference(&need.mask);

        Ok(have.value)
    }

    fn once(&mut self, switch: Switch) -> Result<Term, ConsumeErr> {
        let trans = &self.translate[&switch.name];

        if let Translate::Construct(map) = trans {
            let Resource::Named(named) = &switch.resource else {
                panic!("can only construct named resources")
            };

            let mut heap = HeapConsume {
                inner: self,
                translate: map.clone(),
            };
            (named.typ.fun)(&mut heap, &switch.args)?;

            // TODO: update attribute functions here
            return Ok(());
        }

        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
            name: switch.name,
            span: switch.span,
        };
        let res = self.forall(forall)?.apply(&switch.args);
        Ok(res)
    }
}

impl Heap for HeapProduce<'_> {
    fn forall(&mut self, have: Forall) -> Result<FuncTerm, ConsumeErr> {
        let func = have.resource.associated_func();
        // we want to make sure that expanding the same resource twice gives the same result
        // this is why the values inside the forall are keyed by the parent value
        // TODO: this scope_value might not need to be "leveled" and could be replaced by the one at the root
        let value = FuncTerm::new(move |args| {
            let mut new_args = vec![self.scope_value.clone()];
            new_args.extend_from_slice(args);
            func.apply(&new_args)
        });
        // the resource starts with no indices unpacked
        let part = NewPart {
            resource: have.resource,
            unpacked: vec![],
            mask: have.mask,
            value,
        };

        let existing = self.new_scope.insert(have.name, part);
        assert!(existing.is_none());
        Ok(value)
    }

    fn once(&mut self, switch: Switch) -> Result<Term, ConsumeErr> {
        if let Resource::Impossible = &switch.resource {
            // this automates bringing assumptions into scope
            self.assume.assumptions.push(switch.cond.bool_not());
        }

        // TODO: it would be nice if we did not have to specify indices when using these
        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
            name: switch.name,
            span: switch.span,
        };
        let res = self.forall(forall)?;
        Ok(res.apply(&switch.args))
    }
}

impl SubContext {
    fn try_remove(&mut self, proj: &Proj) -> Result<&mut NewPart, ConsumeErr> {
        let mut obj = &mut self.forall;
        for (name, args) in &proj.parts {
            let part = &obj[name];
            let cond = part.mask.apply_bool(args);
            let last = if self.assume.is_always_true(cond) {
                // we can unpack right now
                part.mask = part.mask.difference(&FuncTerm::exactly(args));
                let Resource::Named(named) = &part.resource else {
                    panic!("can not unpack byte")
                };
                let mut heap = HeapProduce {
                    inner: self,
                    scope_value: part.value.apply(args),
                    new_scope: HashMap::new(),
                };
                (named.typ.fun)(&mut heap, args)?;
                part.unpacked.push(Unpacked {
                    terms: args.clone(),
                    parts: heap.new_scope,
                });
                part.unpacked.last_mut().unwrap()
            } else {
                // maybe it is already unpacked
                part.unpacked
                    .iter_mut()
                    .find(|part| todo!("check that terms is eq to args"))
                    .unwrap()
            };
            obj = &mut last.parts;
        }

        Ok(&mut obj[&proj.last])
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
