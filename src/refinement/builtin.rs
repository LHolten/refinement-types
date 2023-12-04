use std::{
    mem::swap,
    rc::{Rc, Weak},
};

use crate::{
    parse,
    refinement::{func_term::FuncTerm, heap::ConsumeErr, Forall, Resource},
};

use super::{heap::Heap, term::Term, BinOp, Free, Fun, Name, NegTyp, PosTyp, SubContext};

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
            BinOp::Div => self.verify_prop(&r.not_zero()).unwrap(),
            BinOp::Mul => {}
            BinOp::Rem => self.verify_prop(&r.not_zero()).unwrap(),
            BinOp::Eq => {}
            BinOp::Less => {}
            BinOp::And => {}
            BinOp::LessEq => {}
            BinOp::NotEq => {}
            BinOp::MulSafe => {}
        }
    }
}

impl BinOp {
    pub fn apply(&self, l: &Term, r: &Term) -> Term {
        match self {
            BinOp::Add => l.add(r),
            BinOp::Sub => l.sub(r),
            BinOp::Div => l.udiv(r),
            BinOp::Mul => l.mul(r),
            BinOp::Rem => l.urem(r),
            BinOp::Eq => l.eq(r),
            BinOp::Less => l.ult(r),
            BinOp::And => l.bool_and(r),
            BinOp::LessEq => l.ule(r),
            BinOp::NotEq => l.eq(r).is_zero(),
            BinOp::MulSafe => l.umul_no_overlow(r),
        }
    }

    pub fn eval(&self, l: i32, r: i32) -> i32 {
        // TODO: make sure that values wrap arround correct
        match self {
            BinOp::Add => l + r,
            BinOp::Sub => l - r,
            BinOp::Div => l / r,
            BinOp::Mul => l * r,
            BinOp::Rem => l % r,
            BinOp::Eq => (l == r) as i32,
            BinOp::Less => (l < r) as i32,
            BinOp::And => l & r,
            BinOp::LessEq => (l <= r) as i32,
            BinOp::NotEq => (l != r) as i32,
            BinOp::MulSafe => todo!(),
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
    @byte for (ptr) if (ptr - start) < pages;
    assert start <= (start + pages);
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
                    span: named_rc.typ.span,
                    fun: Rc::new(move |heap, args| {
                        let args = args.to_owned();
                        let forall = Forall {
                            named: Resource::Named(named.clone()),
                            mask: FuncTerm::exactly(&args),
                            span: None,
                        };
                        type HeapOp = Box<dyn Fn(&mut dyn Heap) -> Result<(), ConsumeErr>>;
                        let fun = named_rc.typ.fun.clone();
                        let mut need: HeapOp = Box::new(move |heap| {
                            (fun)(heap, &args)?;
                            Ok(())
                        });
                        let mut res: HeapOp = Box::new(move |heap| {
                            heap.forall(forall.clone())?;
                            Ok(())
                        });

                        if unpack {
                            swap(&mut res, &mut need);
                        }
                        (need)(heap)?;

                        Ok(NegTyp::new(Fun {
                            tau: vec![],
                            span: named_rc.typ.span,
                            fun: Rc::new(move |heap, _args| {
                                (res)(heap)?;
                                Ok(PosTyp)
                            }),
                        }))
                    }),
                }
            }
        }
    }
}
