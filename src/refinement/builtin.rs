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
            BinOp::Div => self.assume.verify_prop(&r.not_zero()).unwrap(),
            BinOp::Mul => {}
            BinOp::Rem => self.assume.verify_prop(&r.not_zero()).unwrap(),
            BinOp::Eq => {}
            BinOp::Less => {}
            BinOp::And => {}
            BinOp::Or => {}
            BinOp::LessEq => {}
            BinOp::NotEq => {}
            BinOp::MulSafe => {}
            BinOp::AddSafe => {}
            BinOp::Shl => {}
            BinOp::Shr => {}
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
            BinOp::Or => l.bool_or(r),
            BinOp::LessEq => l.ule(r),
            BinOp::NotEq => l.eq(r).is_zero(),
            BinOp::MulSafe => l.umul_no_overlow(r),
            BinOp::AddSafe => l.uadd_no_overlow(r),
            BinOp::Shl => l.shl(r),
            BinOp::Shr => l.shr(r),
        }
    }

    pub fn eval(&self, l: i32, r: i32) -> i32 {
        let (l, r) = (l as u32, r as u32);
        let res = match self {
            BinOp::Add => l + r,
            BinOp::Sub => l - r,
            BinOp::Div => l / r,
            BinOp::Mul => l * r,
            BinOp::Rem => l % r,
            BinOp::Eq => (l == r) as u32,
            BinOp::Less => (l < r) as u32,
            BinOp::And => l & r,
            BinOp::Or => l | r,
            BinOp::LessEq => (l <= r) as u32,
            BinOp::NotEq => (l != r) as u32,
            BinOp::MulSafe => !l.overflowing_mul(r).1 as u32,
            BinOp::AddSafe => !l.overflowing_add(r).1 as u32,
            BinOp::Shl => l << r,
            BinOp::Shr => l >> r,
        };
        res as i32
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
    [ptr] = @byte if (ptr - start) < pages;
    assert start <= (start + pages);
}";

static READ8: &str = r"
(ptr) where {
    val = @byte(ptr);
} -> (ret) where {
    assert ret == val;
    val;
}";

static READ32: &str = r"
(ptr) where {
    p0 = @byte(ptr + 0);
    p1 = @byte(ptr + 1);
    p2 = @byte(ptr + 2);
    p3 = @byte(ptr + 3);
    let val = ((p3 << 24) + (p2 << 16)) + ((p1 << 8) + p0);
} -> (ret) where {
    assert ret == val;
    p0; p1; p2; p3;
}";

static WRITE8: &str = r"
(ptr, val) where {
    @byte(ptr);
} -> () where {
    new = @byte(ptr);
    assert new == val;
}";

static WRITE32: &str = r"
(ptr, val) where {
    @byte(ptr + 0);
    @byte(ptr + 1);
    @byte(ptr + 2);
    @byte(ptr + 3);
} -> () where {
    p0 = @byte(ptr + 0);
    p1 = @byte(ptr + 1);
    p2 = @byte(ptr + 2);
    p3 = @byte(ptr + 3);
    let new = ((p3 << 24) + (p2 << 16)) + ((p1 << 8) + p0);
    assert new == val;
}";

pub fn builtins() -> Vec<&'static str> {
    vec![ALLOC, READ8, READ32, WRITE8, WRITE32]
}

impl Builtin {
    pub(super) fn infer(&self) -> Fun<NegTyp> {
        let files = builtins();
        match self {
            Builtin::Alloc => desugar::convert_neg(&files, 0),
            Builtin::Read8 => desugar::convert_neg(&files, 1),
            Builtin::Read32 => desugar::convert_neg(&files, 2),
            Builtin::Write8 => desugar::convert_neg(&files, 3),
            Builtin::Write32 => desugar::convert_neg(&files, 4),
            Builtin::Pack(typ) => typ.clone(),
        }
    }
}
