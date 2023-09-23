use super::{Fun, NegTyp};

pub(crate) enum Builtin {
    Read,
    Write,
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
}

impl Builtin {
    pub(super) fn infer(&self) -> Fun<NegTyp> {
        let key = match self {
            Builtin::Read => &READ,
            Builtin::Write => &WRITE,
        };
        key.with(Clone::clone)
    }
}
