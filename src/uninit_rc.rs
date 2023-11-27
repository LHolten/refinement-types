use std::{
    mem::{transmute, MaybeUninit},
    rc::{Rc, UniqueRc, Weak},
};

pub struct UninitRc<T> {
    inner: UniqueRc<MaybeUninit<T>>,
}

impl<T> Default for UninitRc<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> UninitRc<T> {
    pub fn new() -> Self {
        UninitRc {
            inner: UniqueRc::new(MaybeUninit::uninit()),
        }
    }

    pub fn downgrade(&self) -> Weak<T> {
        let weak = UniqueRc::downgrade(&self.inner);
        // SAFETY: the weak reference can only be upgraded after initialization
        unsafe { transmute(weak) }
    }

    pub fn init(mut self, val: T) -> Rc<T> {
        self.inner.write(val);
        let rc = UniqueRc::into_rc(self.inner);
        // SAFETY: the rc has been initialized
        unsafe { transmute(rc) }
    }
}
