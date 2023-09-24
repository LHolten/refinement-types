use std::rc::Rc;

use super::{Prop, Sort, SubContext, Term};

/// a single resource
#[derive(Clone, Debug)]
pub(super) struct Resource {
    pub ptr: Rc<Term>,
    pub value: Rc<Term>,
}

pub(super) trait Heap {
    fn owned(&mut self, ptr: &Rc<Term>, tau: Sort) -> Rc<Term>;
    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>);
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

    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>) {
        self.0.verify_props(&[Prop::Eq(x.clone(), y.clone())]);
    }
}

#[derive(Clone, Debug, Default)]
pub(super) struct HeapProduce {
    pub univ: u32,
    pub alloc: Vec<Resource>,
    pub prop: Vec<Prop>,
}

impl Heap for HeapProduce {
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

    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>) {
        self.prop.push(Prop::Eq(x.clone(), y.clone()));
    }
}
