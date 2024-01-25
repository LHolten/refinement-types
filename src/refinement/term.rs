use std::fmt::Debug;

use z3::{
    ast::{Ast, Bool, Dynamic, BV},
    Sort,
};

use crate::solver::ctx;

#[derive(Clone)]
pub enum Term {
    BV(BV<'static>),
    Bool(Bool<'static>, BV<'static>),
    Uninterp(Dynamic<'static>),
}

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::BV(bv) => bv.fmt(f),
            Term::Bool(b, _) => b.fmt(f),
            Term::Uninterp(u) => u.fmt(f),
        }
    }
}

impl Term {
    pub fn fresh(prefix: &str, size: u32) -> Self {
        Self::BV(BV::fresh_const(ctx(), prefix, size))
    }
    pub fn fresh_uninterpreted() -> Self {
        let sort = Sort::uninterpreted(ctx(), "world".into());
        Self::Uninterp(Dynamic::fresh_const(ctx(), "world", &sort))
    }
    pub fn as_bv(&self) -> &BV<'static> {
        match self {
            Term::BV(bv) => bv,
            Term::Bool(_, bv) => bv,
            Term::Uninterp(_) => panic!(),
        }
    }
    pub fn as_ast(&self) -> &dyn Ast<'static> {
        match self {
            Term::BV(bv) => bv,
            Term::Bool(_, bv) => bv,
            Term::Uninterp(u) => u,
        }
    }
    pub fn get_size(&self) -> u32 {
        match self {
            Term::BV(bv) => bv.get_size(),
            Term::Bool(_, _) => 32,
            Term::Uninterp(_) => panic!(),
        }
    }
    pub fn to_bool(&self) -> Bool<'static> {
        match self {
            Term::BV(bv) => {
                let zero = BV::from_i64(ctx(), 0, bv.get_size());
                zero._eq(bv).not()
            }
            Term::Bool(b, _) => b.clone(),
            Term::Uninterp(_) => panic!(),
        }
    }
    pub fn not_zero(&self) -> Self {
        Self::bool_bv(self.to_bool())
    }
    pub fn is_zero(&self) -> Self {
        match self {
            Term::BV(bv) => {
                let zero = &BV::from_i64(ctx(), 0, bv.get_size());
                Term::bool_bv(zero._eq(bv))
            }
            Term::Bool(b, _) => Term::bool_bv(b.not()),
            Term::Uninterp(_) => panic!(),
        }
    }
    pub fn bool_bv(b: Bool<'static>) -> Self {
        let bv = b.ite(&BV::from_i64(ctx(), 1, 32), &BV::from_i64(ctx(), 0, 32));
        Self::Bool(b, bv)
    }
    pub fn bool(b: bool) -> Self {
        Self::bool_bv(Bool::from_bool(ctx(), b))
    }
    pub fn nat(val: i64, size: u32) -> Self {
        Self::BV(BV::from_i64(ctx(), val, size))
    }
    pub fn add(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvadd(r.as_bv()))
    }
    pub fn sub(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvsub(r.as_bv()))
    }
    pub fn udiv(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvudiv(r.as_bv()))
    }
    pub fn mul(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvmul(r.as_bv()))
    }
    pub fn umul_no_overlow(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.as_bv().bvmul_no_overflow(r.as_bv(), false))
    }
    pub fn uadd_no_overlow(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.as_bv().bvadd_no_overflow(r.as_bv(), false))
    }
    pub fn urem(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvurem(r.as_bv()))
    }
    pub fn eq(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.as_bv()._eq(r.as_bv()))
    }
    pub fn ule(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.as_bv().bvule(r.as_bv()))
    }
    pub fn ult(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.as_bv().bvult(r.as_bv()))
    }
    pub fn shl(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvshl(r.as_bv()))
    }
    pub fn shr(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.as_bv().bvlshr(r.as_bv()))
    }
    pub fn bool_not(&self) -> Self {
        Self::bool_bv(self.to_bool().not())
    }
    pub fn bool_and(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.to_bool() & r.to_bool())
    }
    pub fn bool_or(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.to_bool() | r.to_bool())
    }
    pub fn implies(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::bool_bv(self.to_bool().implies(&r.to_bool()))
    }
    pub fn concat(&self, r: &Self) -> Self {
        Self::BV(self.as_bv().concat(r.as_bv()))
    }
    pub fn extend_to(&self, size: u32) -> Self {
        Self::BV(self.as_bv().zero_ext(size - self.get_size()))
    }
}
