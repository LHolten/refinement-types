use std::fmt::Write;

use indenter::indented;
use z3::{
    ast::{Ast, Bool},
    Model, SatResult, Solver,
};

use crate::solver::solver;

use super::{func_term::FuncTerm, term::Term, CtxForall, Forall, Resource};

impl Forall {
    pub fn make_fresh_args(&self) -> Vec<Term> {
        self.resource
            .arg_sizes()
            .iter()
            .map(|(size, prefix)| Term::fresh(prefix, *size))
            .collect()
    }
}

impl Resource {
    pub fn arg_sizes(&self) -> Vec<(u32, String)> {
        match self {
            Resource::Named(name) => name.typ.tau.clone(),
            Resource::Owned => vec![(32, "@ptr".to_owned())],
        }
    }

    pub fn val_typ(&self) -> Option<usize> {
        match self {
            Resource::Named(name) => Some(name.id),
            Resource::Owned => None,
        }
    }
}

#[derive(Clone, Default)]
pub struct Assume {
    pub assumptions: Vec<Term>,
}

impl Assume {
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
        if large.resource.val_typ() != small.resource.val_typ() {
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

    pub fn verify_prop(&self, prop: &Term) -> Result<(), Model<'static>> {
        let s = self.assume();
        debug_assert_eq!(s.check(), SatResult::Sat);

        match s.check_assumptions(&[prop.to_bool().not()]) {
            SatResult::Unsat => {
                // Yay, verification succeeded
                Ok(())
            }
            SatResult::Unknown => todo!(),
            SatResult::Sat => Err(s.get_model().unwrap()),
        }
    }

    pub fn masked_equal(&self, need: &Forall, l: &FuncTerm, r: &FuncTerm) {
        let s = self.assume();
        let idx = need.make_fresh_args();
        s.assert(&need.mask.apply_bool(&idx));

        match s.check_assumptions(&[l.apply(&idx).eq(&r.apply(&idx)).to_bool().not()]) {
            SatResult::Unsat => {}
            SatResult::Unknown => todo!(),
            SatResult::Sat => {
                panic!("value might be modified")
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

    pub fn counter_example(&mut self, need: Forall, have: &[CtxForall]) -> String {
        let idx = need.make_fresh_args();
        let s = self.assume();
        s.assert(&need.mask.apply_bool(&idx));
        for ctx_forall in have {
            if ctx_forall.have.resource.val_typ() == need.resource.val_typ() {
                s.assert(&ctx_forall.have.mask.apply_bool(&idx).not());
            }
        }
        match s.check() {
            SatResult::Unsat => return "Could not generate a valid counter example".to_owned(),
            SatResult::Unknown => todo!(),
            SatResult::Sat => {}
        }
        let model = s.get_model().unwrap();
        let mut out = String::new();
        let args: Vec<_> = idx
            .iter()
            .map(|idx| model.eval(&idx.to_bv(), true).unwrap().to_string())
            .collect();
        let args = args.join(", ");
        format_model(indented(&mut out), model);
        format!(
            "Here is a valid example for which \n\
            the resource does not exist: \n
            ({args})
            \n{out}"
        )
    }
}

pub fn format_model<F: Write>(mut f: F, model: Model<'_>) {
    writeln!(f, "{model}").unwrap();
    // for x in &model {
    //     let name = x.name();
    //     let name = name.split('!').next().unwrap();
    //     assert_eq!(x.arity(), 0);
    //     let res = model.eval(&x.apply(&[]), false).unwrap();
    //     writeln!(f, "{name} = {}", res.as_bv().unwrap().as_u64().unwrap()).unwrap();
    // }
}

impl Assume {
    pub fn assume(&self) -> &'static Solver<'static> {
        let s = solver();
        s.reset();
        for phi in &self.assumptions {
            s.assert(&phi.to_bool());
        }
        s
    }
}
