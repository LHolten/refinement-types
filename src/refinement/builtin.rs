use std::{mem::swap, rc::Rc};

use crate::refinement::{heap::BoolFuncTerm, Forall};

use super::{heap::Heap, Fun, Name, NegTyp, PosTyp, Term};

pub(crate) enum Builtin {
    Read,
    Write,
    Add,
    Pack(Name, bool),
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
        match self {
            Builtin::Read => READ.with(Clone::clone),
            Builtin::Write => WRITE.with(Clone::clone),
            Builtin::Add => ADD.with(Clone::clone),
            Builtin::Pack(name, unpack) => {
                let func = name.func;
                let unpack = *unpack;
                Fun {
                    tau: name.tau.clone(),
                    fun: Rc::new(move |args, heap| {
                        let args = args.to_owned();
                        let forall = Forall {
                            func,
                            mask: BoolFuncTerm::exactly(&args),
                            arg_num: args.len(),
                        };
                        type HeapOp = Box<dyn Fn(&mut dyn Heap)>;
                        let mut need: HeapOp = Box::new(move |heap| {
                            (func)(heap, &args);
                        });
                        let mut res: HeapOp = Box::new(move |heap| heap.forall(forall.clone()));

                        if unpack {
                            swap(&mut res, &mut need);
                        }
                        (need)(heap);

                        NegTyp::new(Fun {
                            tau: vec![],
                            fun: Rc::new(move |_args, heap| {
                                (res)(heap);
                                PosTyp
                            }),
                        })
                    }),
                }
            }
        }
    }
}
