use std::{
    mem::swap,
    rc::{Rc, Weak},
};

use crate::{
    parse,
    refinement::{heap::FuncTerm, Forall, Resource},
};

use super::{heap::Heap, BinOp, Free, Fun, Name, NegTyp, PosTyp, SubContext, Term};

pub enum Builtin {
    Read,
    Write,
    Pack(Weak<Name>, bool),
    Alloc,
}

impl SubContext {
    pub fn check_binop(&self, op: &BinOp, _l: &Term, r: &Term) {
        // TODO: check int sizes here?
        match op {
            BinOp::Add => {}
            BinOp::Sub => {}
            BinOp::Div => self.verify_prop(&r.not_zero()),
            BinOp::Mul => {}
            BinOp::Eq => {}
            BinOp::Less => {}
            BinOp::And => {}
            BinOp::LessEq => {}
            BinOp::NotEq => {}
        }
    }
}

impl BinOp {
    pub fn apply(&self, l: &Term, r: &Term) -> Term {
        match self {
            BinOp::Add => l.add(r),
            BinOp::Sub => l.sub(r),
            BinOp::Div => todo!(),
            BinOp::Mul => l.mul(r),
            BinOp::Eq => l.eq(r),
            BinOp::Less => l.ult(r),
            BinOp::And => l.bool_and(r),
            BinOp::LessEq => l.ule(r),
            BinOp::NotEq => l.eq(r).is_zero(),
        }
    }

    pub fn eval(&self, l: i64, r: i64) -> i64 {
        // TODO: make sure that values wrap arround correct
        match self {
            BinOp::Add => l + r,
            BinOp::Sub => l - r,
            BinOp::Div => l / r,
            BinOp::Mul => l * r,
            BinOp::Eq => (l == r) as i64,
            BinOp::Less => (l < r) as i64,
            BinOp::And => l & r,
            BinOp::LessEq => (l <= r) as i64,
            BinOp::NotEq => (l != r) as i64,
        }
    }
}

impl Free<Term> {
    pub fn make_term(&self) -> Term {
        match self {
            Free::BinOp { l, r, op } => op.apply(&l.make_term(), &r.make_term()),
            Free::Just(val, size) => Term::nat(*val, *size),
            Free::Var(term) => term.clone(),
        }
    }
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

static ALLOC_STR: &str = r"
(pages) -> (start) where {
    @byte for (ptr) if (start != -1) 
        && (start * 65536 <= ptr)
        && (ptr < (start + pages) * 65536);
    assert (start != -1) => (start <= (start + pages));
    assert (start != -1) => ((start + pages) <= 65536);
}
";

impl Builtin {
    pub(super) fn infer(&self) -> Fun<NegTyp> {
        match self {
            Builtin::Read => READ.with(Clone::clone),
            Builtin::Write => WRITE.with(Clone::clone),
            Builtin::Alloc => parse::convert_neg(ALLOC_STR),
            Builtin::Pack(named, unpack) => {
                let unpack = *unpack;
                let named_rc = named.upgrade().unwrap();
                let named = named.clone();
                Fun {
                    tau: named_rc.typ.tau.clone(),
                    fun: Rc::new(move |heap, args| {
                        let args = args.to_owned();
                        let forall = Forall {
                            named: Resource::Named(named.clone()),
                            mask: FuncTerm::exactly(&args),
                        };
                        type HeapOp = Box<dyn Fn(&mut dyn Heap)>;
                        let fun = named_rc.typ.fun.clone();
                        let mut need: HeapOp = Box::new(move |heap| {
                            (fun)(heap, &args);
                        });
                        let mut res: HeapOp = Box::new(move |heap| {
                            heap.forall(forall.clone());
                        });

                        if unpack {
                            swap(&mut res, &mut need);
                        }
                        (need)(heap);

                        NegTyp::new(Fun {
                            tau: vec![],
                            fun: Rc::new(move |heap, _args| {
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
