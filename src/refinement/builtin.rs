use crate::desugar;

use super::{term::Term, BinOp, Free, Fun, NegTyp, SubContext};

pub enum Builtin {
    Read8,
    Read32,
    Write8,
    Write32,
    Pack(Fun<NegTyp>),
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

static ALLOC: &str = r"
(pages) -> (start) where {
    @byte for (ptr) if (ptr - start) < pages;
    assert start <= (start + pages);
}";

static READ8: &str = r"
(ptr) where {
    val = move @byte(ptr);
} -> (ret) where {
    assert ret == val;
    new = move @byte(ptr);
    assert new == val;
}";

static READ32: &str = r"
(ptr) where {
    val = move @quad(ptr);
} -> (ret) where {
    assert ret == val;
    new = move @byte(ptr);
    assert new == val;
}";

static WRITE8: &str = r"
(ptr, val) where {
    move @byte(ptr);
} -> () where {
    new = move @byte(ptr);
    assert new == val;
}";

static WRITE32: &str = r"
(ptr, val) where {
    move @quad(ptr);
} -> () where {
    new = move @quad(ptr);
    assert new == val;
}";

impl Builtin {
    pub(super) fn infer(&self) -> Fun<NegTyp> {
        match self {
            Builtin::Read8 => desugar::convert_neg(READ8),
            Builtin::Read32 => desugar::convert_neg(READ32),
            Builtin::Write8 => desugar::convert_neg(WRITE8),
            Builtin::Write32 => desugar::convert_neg(WRITE32),
            Builtin::Alloc => desugar::convert_neg(ALLOC),
            Builtin::Pack(typ) => typ.clone(),
        }
    }
}
