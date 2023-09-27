use std::{mem::take, rc::Rc};

use super::{typing::zip_eq, Cond, Context, Fun, FuncDef, NegTyp, Prop, Sort, SubContext, Term};

/// a single resource
#[derive(Clone, Debug)]
pub(super) struct Resource {
    pub ptr: Rc<Term>,
    pub value: Rc<Term>,
}

pub(super) trait Heap {
    fn owned(&mut self, ptr: &Rc<Term>, tau: Sort) -> Rc<Term>;
    fn assert(&mut self, phi: Prop);
    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>) {
        self.assert(Prop::Eq(x.clone(), y.clone()));
    }
    fn func(&mut self, ptr: &Rc<Term>, typ: Fun<NegTyp>);
    fn switch(&mut self, cond: Cond);
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
        let have_typ = self.infer_fptr(ptr);
        self.sub_neg_type(&have_typ, &typ);
    }

    fn switch(&mut self, cond: Cond) {
        // first check if the resource exists as a whole
        let found = self.cond.iter().position(|have| {
            have.func as fn(&'static mut _, u32, &'static _)
                == cond.func as fn(&'static mut _, u32, &'static _)
                && zip_eq(&have.args, &cond.args).all(|(l, r)| self.is_always_eq(l, r))
        });
        if let Some(i) = found {
            self.cond.swap_remove(i);
            return;
        }

        // now we try to build the resource from parts
        eprintln!("&self.cond = {:?}", &self.cond);
        eprintln!("looking for &cond = {:?}", &cond);
        let val = self.get_value(&cond.args[0]);
        (cond.func)(self, val.unwrap(), &cond.args[1..]);
    }

    fn assert(&mut self, phi: Prop) {
        self.verify_props(&[phi.clone()]);
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

    fn switch(&mut self, cond: Cond) {
        let found = self.get_value(&cond.args[0]);

        if let Some(val) = found {
            (cond.func)(self, val, &cond.args[1..]);
        } else {
            self.cond.push(cond)
        }
    }

    fn assert(&mut self, phi: Prop) {
        let next = take(&mut self.assume);
        self.assume = Rc::new(Context::Assume { phi, next });

        let map = self.cond.iter().enumerate().filter_map(|(idx, cond)| {
            let found = self.get_value(&cond.args[0]);
            found.map(|val| (idx, val))
        });
        for (idx, val) in map.rev().collect::<Vec<_>>() {
            let cond = self.cond.swap_remove(idx);
            (cond.func)(self, val, &cond.args[1..]);
        }
    }
}
