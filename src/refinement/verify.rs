use z3::{
    ast::{Ast, Bool, Int},
    SatResult, Solver,
};

use crate::{
    refinement::Sort,
    solver::{ctx, solver},
};

use super::{Context, Prop, SubContext, Term};

impl From<&Term> for Int<'_> {
    fn from(value: &Term) -> Self {
        let ctx = ctx();
        match value {
            Term::UVar(var, tau) => {
                assert_eq!(*tau, Sort::Nat);
                Int::new_const(ctx, *var)
            }
            Term::Nat(val) => Int::from_u64(ctx, *val as u64),
        }
    }
}

impl From<&Prop> for Bool<'_> {
    fn from(value: &Prop) -> Self {
        match value {
            Prop::Eq(l, r) => Int::from(l.as_ref())._eq(&Int::from(r.as_ref())),
        }
    }
}

impl SubContext {
    pub fn is_always_eq(&self, l: &Term, r: &Term) -> bool {
        let s = self.assume.assume();
        let cond = Int::from(l)._eq(&Int::from(r));

        match s.check_assumptions(&[cond.not()]) {
            SatResult::Unsat => true,
            SatResult::Unknown => todo!(),
            SatResult::Sat => false,
        }
        // eprintln!("{:?}", &self.assume);
        // eprintln!("=> {:?}", phi);
    }

    pub fn verify_props(&self, props: &[Prop]) {
        let s = self.assume.assume();
        for prop in props {
            match s.check_assumptions(&[Bool::from(prop).not()]) {
                SatResult::Unsat => {
                    // Yay, verification succeeded
                }
                SatResult::Unknown => todo!(),
                SatResult::Sat => panic!(),
            }
        }

        eprintln!("{:?}", &self.assume);
    }
}

impl Context {
    pub fn assume(&self) -> &'static Solver<'static> {
        match self {
            Context::Empty => {
                let s = solver();
                s.reset();
                s
            }
            Context::Assume { phi, next } => {
                let s = next.assume();
                s.assert(&Bool::from(phi));
                s
            }
        }
    }
}
