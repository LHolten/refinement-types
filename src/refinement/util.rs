use std::{fmt::Debug, ops::Deref, rc::Rc};

pub struct Opaque<T: ?Sized>(pub Rc<T>);

impl<T> Opaque<T> {
    pub fn new(val: T) -> Opaque<T> {
        Self(Rc::new(val))
    }
}

impl<T: ?Sized> Debug for Opaque<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Opaque").finish()
    }
}

impl<T: ?Sized> PartialEq for Opaque<T> {
    fn eq(&self, _other: &Self) -> bool {
        panic!()
    }
}

impl<T: ?Sized> Eq for Opaque<T> {}
impl<T: ?Sized> Clone for Opaque<T> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<T: ?Sized> Deref for Opaque<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
