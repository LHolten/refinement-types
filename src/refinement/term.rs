use std::fmt::Debug;

use z3::ast::{Ast, Bool, BV};

use crate::solver::ctx;

#[derive(Clone)]
pub enum Term {
    BV(BV<'static>),
    Bool(Bool<'static>),
}

impl Debug for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Term::BV(bv) => bv.fmt(f),
            Term::Bool(b) => b.fmt(f),
        }
    }
}

impl Term {
    pub fn fresh(prefix: &str, size: u32) -> Self {
        Self::BV(BV::fresh_const(ctx(), prefix, size))
    }
    pub fn to_bv(&self) -> BV<'static> {
        match self {
            Term::BV(bv) => bv.clone(),
            Term::Bool(b) => b.ite(&BV::from_i64(ctx(), 1, 32), &BV::from_i64(ctx(), 0, 32)),
        }
    }
    pub fn get_size(&self) -> u32 {
        match self {
            Term::BV(bv) => bv.get_size(),
            Term::Bool(_) => 32,
        }
    }
    pub fn to_bool(&self) -> Bool<'static> {
        match self {
            Term::BV(bv) => {
                let zero = BV::from_i64(ctx(), 0, bv.get_size());
                zero._eq(bv).not()
            }
            Term::Bool(b) => b.clone(),
        }
    }
    pub fn not_zero(&self) -> Self {
        Self::Bool(self.to_bool())
    }
    pub fn is_zero(&self) -> Self {
        match self {
            Term::BV(bv) => {
                let zero = &BV::from_i64(ctx(), 0, bv.get_size());
                Term::Bool(zero._eq(bv))
            }
            Term::Bool(b) => Term::Bool(b.not()),
        }
    }
    pub fn bool(b: bool) -> Self {
        Self::Bool(Bool::from_bool(ctx(), b))
    }
    pub fn nat(val: i64, size: u32) -> Self {
        Self::BV(BV::from_i64(ctx(), val, size))
    }
    pub fn add(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvadd(&r.to_bv()))
    }
    pub fn sub(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvsub(&r.to_bv()))
    }
    pub fn udiv(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvudiv(&r.to_bv()))
    }
    pub fn mul(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvmul(&r.to_bv()))
    }
    pub fn umul_no_overlow(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bv().bvmul_no_overflow(&r.to_bv(), false))
    }
    pub fn uadd_no_overlow(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bv().bvadd_no_overflow(&r.to_bv(), false))
    }
    pub fn urem(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvurem(&r.to_bv()))
    }
    pub fn eq(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bv()._eq(&r.to_bv()))
    }
    pub fn ule(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bv().bvule(&r.to_bv()))
    }
    pub fn ult(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bv().bvult(&r.to_bv()))
    }
    pub fn shl(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvshl(&r.to_bv()))
    }
    pub fn shr(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::BV(self.to_bv().bvlshr(&r.to_bv()))
    }
    pub fn bool_and(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bool() & r.to_bool())
    }
    pub fn bool_or(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bool() | r.to_bool())
    }
    pub fn implies(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bool().implies(&r.to_bool()))
    }
    pub fn concat(&self, r: &Self) -> Self {
        Self::BV(self.to_bv().concat(&r.to_bv()))
    }
    pub fn extend_to(&self, size: u32) -> Self {
        Self::BV(self.to_bv().zero_ext(size - self.get_size()))
    }
}
