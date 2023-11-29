use std::{
    cell::RefCell,
    fmt::Write,
    mem::take,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use indenter::indented;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::{ast::Bool, FuncDecl, Model, Sort};

use crate::solver::ctx;

use super::{typing::zip_eq, Cond, CtxForall, Forall, Resource, SubContext, Term};

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub enum FuncTerm {
    Free(Rc<FuncDecl<'static>>),
    User(Rc<dyn Fn(&[Term]) -> Term>),
}

impl FuncTerm {
    pub fn new<F: Fn(&[Term]) -> Term + 'static>(f: F) -> Self {
        Self::User(Rc::new(f))
    }

    pub fn new_bool<F: Fn(&[Term]) -> Bool<'static> + 'static>(f: F) -> Self {
        Self::new(move |x| Term::Bool((f)(x)))
    }

    pub fn apply_bool(&self, idx: &[Term]) -> Bool<'static> {
        self.apply(idx).to_bool()
    }

    pub fn apply(&self, idx: &[Term]) -> Term {
        match self {
            FuncTerm::Free(f) => {
                let args: Vec<_> = idx.iter().map(|x| x.to_bv()).collect();
                let args: Vec<_> = args.iter().map(|x| x as _).collect();
                let val = f.apply(&args);
                if let Some(b) = val.as_bool() {
                    Term::Bool(b)
                } else if let Some(bv) = val.as_bv() {
                    Term::BV(bv)
                } else {
                    panic!()
                }
            }
            FuncTerm::User(func) => (func)(idx),
        }
    }

    pub fn difference(&self, other: &Self) -> Self {
        let this = self.clone();
        let other = other.clone();
        Self::new_bool(move |idx| this.apply_bool(idx) & !other.apply_bool(idx))
    }

    pub fn ite(&self, then: &Self, other: &Self) -> Self {
        let (cond, then, other) = (self.clone(), then.clone(), other.clone());
        Self::new(move |idx| {
            let (then, other) = (then.apply(idx).to_bv(), other.apply(idx).to_bv());
            assert_eq!(then.get_size(), other.get_size());
            Term::BV(cond.apply_bool(idx).ite(&then, &other))
        })
    }

    pub fn exactly(ptr: &[Term]) -> Self {
        let ptr = ptr.to_owned();
        Self::new_bool(move |val| {
            zip_eq(&ptr, val)
                .map(|(l, r)| l.eq(r).to_bool())
                .fold(Bool::from_bool(ctx(), true), |l, r| l & r)
        })
    }

    pub fn and(&self, other: &Self) -> Self {
        let this = self.clone();
        let other = other.clone();
        Self::new_bool(move |idx| this.apply_bool(idx) & other.apply_bool(idx))
    }

    fn free(arg_size: &[(u32, String)]) -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        let name = format!("heap-{}", ID.fetch_add(1, Ordering::Relaxed));
        let domain: Vec<_> = arg_size
            .iter()
            .map(|(sz, _name)| Sort::bitvector(ctx(), *sz))
            .collect();
        let domain: Vec<_> = domain.iter().collect();
        let f = FuncDecl::new(ctx(), name, &domain, &Sort::bitvector(ctx(), 8));
        Self::Free(Rc::new(f))
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

pub fn format_model<F: Write>(mut f: F, model: Model<'_>) {
    for x in &model {
        let name = x.name();
        let name = name.split('!').next().unwrap();
        let res = model.eval(&x.apply(&[]), false).unwrap();
        writeln!(f, "{name} = {}", res.as_bv().unwrap().as_u64().unwrap()).unwrap();
    }
}

impl SubContext {
    fn counter_example(&mut self, need: Forall) -> String {
        let idx = need.make_fresh_args();
        let s = self.assume();
        s.assert(&need.mask.apply_bool(&idx));
        for ctx_forall in &self.forall {
            if ctx_forall.have.id() == need.id() {
                s.assert(&ctx_forall.have.mask.apply_bool(&idx).not());
            }
        }
        s.check();
        let model = s.get_model().unwrap();
        let mut out = String::new();
        format_model(indented(&mut out), model);
        format!(
            "Here is a valid example for which \n\
            the resource does not exist: \n{out}"
        )
    }

    fn try_remove(&mut self, need: Forall) -> Result<FuncTerm, Forall> {
        let required = RefCell::new(need);
        let mut forall_list = take(&mut self.forall);
        let mut removals = vec![];

        // first we consume small allocations
        for alloc in forall_list
            .extract_if(|ctx_forall| self.always_contains(&required.borrow(), &ctx_forall.have))
        {
            let new_mask = required.borrow().mask.difference(&alloc.have.mask);
            required.borrow_mut().mask = new_mask;
            removals.push(Removal {
                mask: alloc.have.mask,
                value: alloc.value,
            })
        }
        self.forall = forall_list;
        let required = required.into_inner();

        if !self.still_possible(&required) {
            let value = build_value(removals, None);
            return Ok(value);
        }

        // then we find a larger allocation to take the remainder from
        let idx = self
            .forall
            .iter()
            .position(|ctx_forall| self.always_contains(&ctx_forall.have, &required));
        let Some(idx) = idx else {
            return Err(required);
        };

        let ctx_forall = &mut self.forall[idx];
        // regions can not be equal in size, it would already be consumed
        ctx_forall.have.mask = ctx_forall.have.mask.difference(&required.mask);

        let value = build_value(removals, Some(ctx_forall.value.clone()));
        Ok(value)
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

#[derive(Debug, Diagnostic, Error)]
pub enum ConsumeErr {
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
