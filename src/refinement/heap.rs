use std::{cell::RefCell, mem::take, rc::Rc};

use z3::ast::Bool;

use crate::solver::ctx;

use super::{typing::zip_eq, Cond, Forall, Fun, FuncDef, NegTyp, Resource, SubContext, Term};

#[allow(clippy::type_complexity)]
pub enum BoolFuncTerm {
    User(Box<dyn Fn(&[Term]) -> Bool<'static>>),
}

impl BoolFuncTerm {
    pub fn new<F: Fn(&[Term]) -> Bool<'static> + 'static>(f: F) -> Rc<Self> {
        Rc::new(Self::User(Box::new(f)))
    }

    pub fn apply(&self, idx: &[Term]) -> Bool<'static> {
        match self {
            BoolFuncTerm::User(func) => (func)(idx),
        }
    }

    pub fn difference(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self> {
        let this = self.clone();
        let other = other.clone();
        Self::new(move |idx| this.apply(idx) & !other.apply(idx))
    }

    pub fn exactly(ptr: &[Term]) -> Rc<Self> {
        let ptr = ptr.to_owned();
        Self::new(move |val| {
            zip_eq(&ptr, val)
                .map(|(l, r)| l.eq(r).to_bool())
                .fold(Bool::from_bool(ctx(), true), |l, r| l & r)
        })
    }

    pub fn and(self: &Rc<Self>, other: &Rc<Self>) -> Rc<Self> {
        let this = self.clone();
        let other = other.clone();
        Self::new(move |idx| this.apply(idx) & other.apply(idx))
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
    fn owned_byte(&mut self, ptr: &Term) -> Term;
    fn assert(&mut self, phi: Term);
    fn assert_eq(&mut self, x: &Term, y: &Term) {
        self.assert(x.eq(y));
    }
    fn func(&mut self, ptr: &Term, typ: Fun<NegTyp>);
    fn forall(&mut self, forall: Forall);
    fn switch(&mut self, cond: Cond) {
        let condition = BoolFuncTerm::new(move |_| cond.cond.to_bool());
        self.forall(Forall {
            named: cond.named,
            mask: BoolFuncTerm::exactly(&cond.args).and(&condition),
        })
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
        let condition = BoolFuncTerm::new(move |_| cond.cond.to_bool());
        let need = Forall {
            named: cond.named.clone(),
            mask: BoolFuncTerm::exactly(&cond.args).and(&condition),
        };

        if let Some(need) = self.try_remove(need) {
            let res = need.mask.apply(&cond.args);
            if self.is_always_true(res) {
                (cond.named.upgrade().unwrap().typ.fun)(self, &cond.args);
            } else {
                panic!("can not pack named resource")
            }
        }
    }

    fn owned_byte(&mut self, ptr: &Term) -> Term {
        let mut found = None;
        for (idx, alloc) in self.alloc.iter().enumerate() {
            if self.is_always_eq(&alloc.ptr, ptr) {
                found = Some(idx);
                break;
            }
        }
        let Some(idx) = found else {
            panic!("could not find owned byte")
        };
        let resource = self.alloc.swap_remove(idx);
        resource.value
    }

    fn func(&mut self, ptr: &Term, typ: Fun<NegTyp>) {
        let have_typ = self.infer_fptr(ptr);

        // We do not want to allow access to resources outside the function
        // Technically we can allow access if the access is read only
        // Checking that the final resource is identical is not enough
        // (Different closures could use the same memory)
        let this = self.without_alloc();
        this.sub_neg_type(have_typ, &typ);
    }

    /// We can first look at aggregate resources of the correct name.
    /// After that we can iterate over the remaining resources one by one.
    fn forall(&mut self, need: Forall) {
        if let Some(need) = self.try_remove(need) {
            let idx = need.make_fresh_args();
            for have in &self.forall {
                if have.named.upgrade().unwrap().id == need.named.upgrade().unwrap().id {
                    println!("have {}", have.mask.apply(&idx))
                }
            }
            for assume in &self.assume {
                println!("assume {assume:?}");
            }
            panic!("missing {}", need.mask.apply(&idx));
        }
    }

    fn assert(&mut self, phi: Term) {
        self.verify_prop(&phi);
    }
}

impl SubContext {
    fn try_remove(&mut self, need: Forall) -> Option<Forall> {
        let required = RefCell::new(need);
        let mut forall_list = take(&mut self.forall);

        // first we consume small allocations
        for alloc in forall_list.extract_if(|have| self.always_contains(&required.borrow(), have)) {
            let new_mask = required.borrow().mask.difference(&alloc.mask);
            required.borrow_mut().mask = new_mask;
        }
        self.forall = forall_list;
        let required = required.into_inner();

        if !self.still_possible(&required) {
            return None;
        }

        // then we find a larger allocation to take the remainder from
        let idx = self
            .forall
            .iter()
            .position(|have| self.always_contains(have, &required));
        let Some(idx) = idx else {
            return Some(required);
        };

        let have = &mut self.forall[idx];
        // regions can not be equal in size, it would already be consumed
        have.mask = have.mask.difference(&required.mask);

        None
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
    fn owned_byte(&mut self, ptr: &Term) -> Term {
        let val = Term::fresh("heap", 8);
        self.alloc.push(Resource {
            ptr: ptr.clone(),
            value: val.clone(),
        });
        val
    }

    fn func(&mut self, ptr: &Term, typ: Fun<NegTyp>) {
        self.funcs.push(FuncDef {
            ptr: ptr.clone(),
            typ: typ.clone(),
        })
    }

    /// Here we just put the aggregate to be used by consumption.
    fn forall(&mut self, forall: Forall) {
        self.forall.push(forall);
    }

    fn assert(&mut self, phi: Term) {
        self.assume.push(phi);
    }
}
