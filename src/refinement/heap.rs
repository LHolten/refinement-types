use std::{mem::take, rc::Rc};

use super::{Cond, Context, Fun, FuncDef, NegTyp, Prop, Sort, SubContext, Term};

/// a single resource
#[derive(Clone, Debug)]
pub(super) struct Resource {
    pub ptr: Rc<Term>,
    pub value: Rc<Term>,
}

pub(super) trait Heap {
    fn owned(&mut self, ptr: &Rc<Term>, tau: Sort) -> Rc<Term>;
    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>);
    fn func(&mut self, ptr: &Rc<Term>, typ: Fun<NegTyp>);
    fn switch(&mut self, c: Cond);
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
    fn owned(&mut self, ptr: &Rc<Term>, tau: Sort) -> Rc<Term> {
        let mut found = None;
        for (idx, alloc) in self.alloc.iter().enumerate() {
            if self.is_always_eq(&alloc.ptr, ptr) {
                found = Some(idx);
                break;
            }
        }
        let resource = self.alloc.swap_remove(found.unwrap());
        // TODO: check that resource has correct sort
        assert_eq!(tau, Sort::Nat);
        resource.value
    }

    fn func(&mut self, ptr: &Rc<Term>, typ: Fun<NegTyp>) {
        let have_typ = self.infer_fptr(&ptr);
        self.sub_neg_type(&have_typ, &typ);
    }

    fn switch(&mut self, c: Cond) {
        let mut found = None;
        for i in 0..c.branch.len() {
            if self.is_always_eq(&c.arg, &Term::Nat(i)) {
                found = Some(i);
                break;
            }
        }
        if let Some(i) = found {
            (c.branch[i])(self);
        } else {
            self.cond.push(c)
        }
    }

    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>) {
        self.verify_props(&[Prop::Eq(x.clone(), y.clone())]);
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
    /// all uses of `alloc` are recorded as resources
    fn owned(&mut self, ptr: &Rc<Term>, tau: Sort) -> Rc<Term> {
        let val = Rc::new(Term::UVar(self.univ, tau));
        self.univ += 1;
        self.alloc.push(Resource {
            ptr: ptr.clone(),
            value: val.clone(),
        });
        val
    }

    fn func(&mut self, ptr: &Rc<Term>, typ: Fun<NegTyp>) {
        self.funcs.push(FuncDef {
            ptr: ptr.clone(),
            typ: typ.clone(),
        })
    }

    fn switch(&mut self, c: Cond) {
        let mut found = None;
        for i in 0..c.branch.len() {
            if self.is_always_eq(&c.arg, &Term::Nat(i)) {
                found = Some(i);
                break;
            }
        }
        if let Some(i) = found {
            (c.branch[i])(self);
        } else {
            // TODO: remove the cond from the list somehow
        }
    }

    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>) {
        let phi = Prop::Eq(x.clone(), y.clone());
        let next = take(&mut self.assume);
        self.assume = Rc::new(Context::Assume { phi, next });
    }
}
