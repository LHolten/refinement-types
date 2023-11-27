use z3::{
    ast::{Ast, Bool, BV},
    SatResult, Solver,
};

use crate::solver::{ctx, solver};

use super::{Forall, Resource, SubContext, Term};

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
    pub fn bool_and(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::Bool(self.to_bool() & r.to_bool())
    }
    pub fn concat(&self, r: &Self) -> Self {
        Self::BV(self.to_bv().concat(&r.to_bv()))
    }
    pub fn extend_to(&self, size: u32) -> Self {
        Self::BV(self.to_bv().zero_ext(size - self.get_size()))
    }
}

impl Forall {
    pub fn make_fresh_args(&self) -> Vec<Term> {
        self.arg_sizes()
            .iter()
            .map(|size| Term::fresh("index", *size))
            .collect()
    }
    pub fn id(&self) -> Option<usize> {
        match &self.named {
            Resource::Named(name) => Some(name.upgrade().unwrap().id),
            Resource::Owned => None,
        }
    }
    pub fn arg_sizes(&self) -> Vec<u32> {
        match &self.named {
            Resource::Named(name) => name.upgrade().unwrap().typ.tau.clone(),
            Resource::Owned => vec![32],
        }
    }
}

impl SubContext {
    pub fn is_always_true(&self, cond: Bool<'static>) -> bool {
        let s = self.assume();
        debug_assert_eq!(s.check(), SatResult::Sat);

        match s.check_assumptions(&[cond.not()]) {
            SatResult::Unsat => true,
            SatResult::Unknown => todo!(),
            SatResult::Sat => false,
        }
    }

    pub fn still_possible(&self, forall: &Forall) -> bool {
        let s = self.assume();
        debug_assert_eq!(s.check(), SatResult::Sat);

        let idx = forall.make_fresh_args();
        let cond = forall.mask.apply_bool(&idx);

        match s.check_assumptions(&[cond]) {
            SatResult::Unsat => false,
            SatResult::Unknown => todo!(),
            SatResult::Sat => true,
        }
    }

    pub fn exactly_equal() {}
    pub fn never_overlap() {}
    pub fn always_contains(&self, large: &Forall, small: &Forall) -> bool {
        if large.id() != small.id() {
            return false;
        }
        // debug_assert_eq!(large_named.typ.tau, small_named.typ.tau);
        let idx = large.make_fresh_args();

        let cond = small
            .mask
            .apply_bool(&idx)
            .implies(&large.mask.apply_bool(&idx));
        self.is_always_true(cond)
    }

    pub fn is_always_eq(&self, l: &Term, r: &Term) -> bool {
        let cond = l.eq(r).to_bool();
        self.is_always_true(cond)
    }

    pub fn verify_prop(&self, prop: &Term) {
        let s = self.assume();
        debug_assert_eq!(s.check(), SatResult::Sat);

        match s.check_assumptions(&[prop.to_bool().not()]) {
            SatResult::Unsat => {
                // Yay, verification succeeded
            }
            SatResult::Unknown => todo!(),
            SatResult::Sat => {
                eprintln!("{:?}", &self.assume);
                eprintln!("=> {:?}", prop);
                let model = s.get_model().unwrap();
                panic!("failed to verify {model}")
            }
        }
    }

    pub fn get_value(&self, term: &Term) -> Option<u32> {
        let s = self.assume();
        let term = &term.to_bv();
        match s.check() {
            SatResult::Unsat => todo!(),
            SatResult::Unknown => todo!(),
            SatResult::Sat => {
                let model = s.get_model().unwrap();
                let val = model.eval(term, true).unwrap();

                match s.check_assumptions(&[term._eq(&val).not()]) {
                    SatResult::Unsat => Some(val.as_u64().unwrap() as u32),
                    SatResult::Unknown => todo!(),
                    SatResult::Sat => None,
                }
            }
        }
    }
}

impl SubContext {
    pub fn assume(&self) -> &'static Solver<'static> {
        let s = solver();
        s.reset();
        for phi in &self.assume {
            s.assert(&phi.to_bool());
        }
        s
    }
}
