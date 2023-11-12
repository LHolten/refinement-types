use z3::{
    ast::{Ast, Bool, Int},
    SatResult, Solver,
};

use crate::solver::{ctx, solver};

use super::{Forall, Prop, SubContext, Term};

impl From<&Term> for Int<'_> {
    fn from(value: &Term) -> Self {
        let ctx = ctx();
        match value {
            Term::UVar(var, _tau) => var.clone(),
            Term::Ite(cond, t, e) => cond.ite(&Int::from(t.as_ref()), &Int::from(e.as_ref())),
            Term::Nat(val) => Int::from_i64(ctx, *val),
            Term::Add(l, r) => Int::add(ctx, &[&Int::from(l.as_ref()), &Int::from(r.as_ref())]),
            Term::Bool(b) => {
                Bool::from(b.as_ref()).ite(&Int::from_i64(ctx, 1), &Int::from_i64(ctx, 0))
            }
        }
    }
}

impl From<&Prop> for Bool<'_> {
    fn from(value: &Prop) -> Self {
        match value {
            Prop::Uvar(b) => b.clone(),
            Prop::Eq(l, r) => Int::from(l.as_ref())._eq(&Int::from(r.as_ref())),
            Prop::LessEq(l, r) => Int::from(l.as_ref()).le(&Int::from(r.as_ref())),
        }
    }
}

impl SubContext {
    pub fn is_always_true(&self, cond: Bool<'_>) -> bool {
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

        let idx: Vec<_> = std::iter::repeat_with(|| Int::fresh_const(ctx(), "index"))
            .take(forall.arg_num)
            .collect();
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
        assert_eq!(large.arg_num, small.arg_num);
        let idx: Vec<_> = std::iter::repeat_with(|| Int::fresh_const(ctx(), "index"))
            .take(large.arg_num)
            .collect();

        let cond = small.mask.apply(&idx).implies(&large.mask.apply(&idx));
        self.is_always_true(cond)
    }

    pub fn is_always_eq(&self, l: &Term, r: &Term) -> bool {
        let cond = Int::from(l)._eq(&Int::from(r));
        self.is_always_true(cond)
    }

    pub fn verify_props(&self, props: &[Prop]) {
        let s = self.assume();
        debug_assert_eq!(s.check(), SatResult::Sat);

        for prop in props {
            match s.check_assumptions(&[Bool::from(prop).not()]) {
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
    }

    pub fn get_value(&self, term: &Term) -> Option<u32> {
        let s = self.assume();
        let term = Int::from(term);
        match s.check() {
            SatResult::Unsat => todo!(),
            SatResult::Unknown => todo!(),
            SatResult::Sat => {
                let model = s.get_model().unwrap();
                let val = model.eval(&term, true).unwrap();

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
            s.assert(&Bool::from(phi));
        }
        s
    }
}
