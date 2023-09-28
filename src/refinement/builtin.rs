use std::rc::Rc;

use super::{heap::Heap, Fun, NegTyp, Term};

pub(crate) enum Builtin {
    Read,
    Write,
    Add,
}

fn add_cond(heap: &mut dyn Heap, sum: &Rc<Term>, l: &Rc<Term>, r: &Rc<Term>) {
    heap.assert_eq(sum, &Rc::new(Term::Add(l.clone(), r.clone())))
}

// TODO: these leak a bit of memory for each thread
thread_local! {
    static READ: Fun<NegTyp> = neg_typ!(
        (ptr:Nat) where {let val = ptr[0]}
            -> (ret:Nat) where {ret == val; let new = ptr[0]; new == val}
    );
    static WRITE: Fun<NegTyp> = neg_typ!(
        (ptr:Nat, val:Nat) where {let _ = ptr[0]}
            -> () where {let new = ptr[0]; new == val}
    );
    static ADD: Fun<NegTyp> = neg_typ!(
        (l:Nat, r:Nat) -> (sum:Nat) where {add_cond(sum, l, r)}
    );
}

impl Builtin {
    pub(super) fn infer(&self) -> Fun<NegTyp> {
        let key = match self {
            Builtin::Read => &READ,
            Builtin::Write => &WRITE,
            Builtin::Add => &ADD,
        };
        key.with(Clone::clone)
    }
}
