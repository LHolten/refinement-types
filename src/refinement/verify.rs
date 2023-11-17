use z3::{
    ast::{Ast, Bool, BV},
    SatResult, Solver,
};

use crate::solver::{ctx, solver};

use super::{Forall, SubContext, Term};

impl Term {
    pub fn fresh(prefix: &str, size: u32) -> Self {
        Self(BV::fresh_const(ctx(), prefix, size))
    }
    fn from_bool(b: Bool<'static>) -> Self {
        Self(b.ite(&BV::from_i64(ctx(), 1, 32), &BV::from_i64(ctx(), 0, 32)))
    }

    pub fn get_size(&self) -> u32 {
        self.0.get_size()
    }
    pub fn to_bool(&self) -> Bool<'static> {
        let size = self.get_size();
        let zero = BV::from_i64(ctx(), 0, size);
        self.0._eq(&zero).not()
    }
    pub fn bool(b: bool) -> Self {
        Self::nat(b as i64, 32)
    }
    pub fn nat(val: i64, size: u32) -> Self {
        Self(BV::from_i64(ctx(), val, size))
    }
    pub fn add(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self(self.0.bvadd(&r.0))
    }
    pub fn eq(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::from_bool(self.0._eq(&r.0))
    }
    pub fn ule(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::from_bool(self.0.bvule(&r.0))
    }
    pub fn ult(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self::from_bool(self.0.bvult(&r.0))
    }
    pub fn and(&self, r: &Self) -> Self {
        assert_eq!(self.get_size(), r.get_size());
        Self(self.0.bvand(&r.0))
    }
    pub fn not(&self) -> Self {
        Self(self.0.bvnot())
    }
    pub fn not_zero(&self) -> Self {
        Self::from_bool(self.to_bool())
    }
    pub fn concat(&self, r: &Self) -> Self {
        Self(self.0.concat(&r.0))
    }
    pub fn extend_to(&self, size: u32) -> Self {
        Self(self.0.zero_ext(size - self.get_size()))
    }
}

impl Forall {
    pub fn make_fresh_args(&self) -> Vec<Term> {
        self.arg_size
            .iter()
            .map(|size| Term::fresh("index", *size))
            .collect()
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
        let cond = forall.mask.apply(&idx);

        match s.check_assumptions(&[cond]) {
            SatResult::Unsat => false,
            SatResult::Unknown => todo!(),
            SatResult::Sat => true,
        }
    }

    pub fn exactly_equal() {}
    pub fn never_overlap() {}
    pub fn always_contains(&self, large: &Forall, small: &Forall) -> bool {
        if large.func as fn(&'static mut _, &'static _)
            != small.func as fn(&'static mut _, &'static _)
        {
            return false;
        }
        assert_eq!(large.arg_size, small.arg_size);
        let idx = large.make_fresh_args();

        let cond = small.mask.apply(&idx).implies(&large.mask.apply(&idx));
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
                panic!("failed to verify")
            }
        }
    }

    pub fn get_value(&self, term: &Term) -> Option<u32> {
        let s = self.assume();
        let term = &term.0;
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
