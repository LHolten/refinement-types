use std::{
    cell::RefCell,
    mem::take,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use z3::{ast::Bool, FuncDecl, Sort};

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

    fn free(arg_size: &[u32]) -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        let name = format!("heap-{}", ID.fetch_add(1, Ordering::Relaxed));
        let domain: Vec<_> = arg_size
            .iter()
            .map(|sz| Sort::bitvector(ctx(), *sz))
            .collect();
        let domain: Vec<_> = domain.iter().collect();
        let f = FuncDecl::new(ctx(), name, &domain, &Sort::bitvector(ctx(), 8));
        Self::Free(Rc::new(f))
    }
}

pub trait Heap {
    // load bytes and store in size bits
    fn owned(&mut self, ptr: &Term, bytes: u32, size: u32) -> Term {
        let mut res = self.owned_byte(ptr);
        let mut ptr = ptr.clone();
        for _ in 1..bytes {
            ptr = ptr.add(&Term::nat(1, 32));
            // little endian, so new value is more significant
            let val = self.owned_byte(&ptr);
            res = val.concat(&res);
        }
        res.extend_to(size)
    }
    fn owned_byte(&mut self, ptr: &Term) -> Term {
        let value = self.forall(Forall {
            named: Resource::Owned,
            mask: FuncTerm::exactly(&[ptr.to_owned()]),
        });
        value.apply(&[ptr.to_owned()])
    }
    fn assert(&mut self, phi: Term);
    fn assert_eq(&mut self, x: &Term, y: &Term) {
        self.assert(x.eq(y));
    }
    fn forall(&mut self, forall: Forall) -> FuncTerm;
    fn switch(&mut self, cond: Cond) {
        let condition = FuncTerm::new_bool(move |_| cond.cond.to_bool());
        self.forall(Forall {
            named: Resource::Named(cond.named),
            mask: FuncTerm::exactly(&cond.args).and(&condition),
        });
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
    fn switch(&mut self, cond: Cond) {
        let condition = FuncTerm::new_bool(move |_| cond.cond.to_bool());
        let need = Forall {
            named: Resource::Named(cond.named.clone()),
            mask: FuncTerm::exactly(&cond.args).and(&condition),
        };

        if let Err(need) = self.try_remove(need) {
            let res = need.mask.apply_bool(&cond.args);
            if self.is_always_true(res) {
                (cond.named.upgrade().unwrap().typ.fun)(self, &cond.args);
            } else {
                panic!("can not pack named resource")
            }
        }
    }

    /// We can first look at aggregate resources of the correct name.
    /// After that we can iterate over the remaining resources one by one.
    fn forall(&mut self, need: Forall) -> FuncTerm {
        match self.try_remove(need) {
            Ok(res) => res,
            Err(need) => {
                let idx = need.make_fresh_args();
                for ctx_forall in &self.forall {
                    if ctx_forall.have.id() == need.id() {
                        println!("have {}", ctx_forall.have.mask.apply_bool(&idx))
                    }
                }
                for assume in &self.assume {
                    println!("assume {assume:?}");
                }
                panic!("missing {}", need.mask.apply_bool(&idx));
            }
        }
    }

    fn assert(&mut self, phi: Term) {
        self.verify_prop(&phi);
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

impl SubContext {
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
    fn forall(&mut self, forall: Forall) -> FuncTerm {
        let value = FuncTerm::free(&forall.arg_sizes());
        self.forall.push(CtxForall {
            have: forall,
            value: value.clone(),
        });
        value
    }

    fn assert(&mut self, phi: Term) {
        self.assume.push(phi);
    }
}
