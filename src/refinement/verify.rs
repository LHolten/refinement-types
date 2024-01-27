use std::{
    collections::HashMap,
    fmt::{self, Write},
};

use indenter::indented;
use z3::{
    ast::{Ast, Bool},
    Model, SatResult, Solver,
};

use crate::{solver::solver, Nested};

use super::{func_term::FuncTerm, heap::NewPart, term::Term, CtxForall, Forall, Resource};

impl Resource {
    pub fn make_fresh_args(&self) -> Vec<Term> {
        self.arg_sizes()
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
            Resource::Impossible => vec![],
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

    pub fn still_possible(&self, forall: &NewPart) -> bool {
        let s = self.assume();
        debug_assert_eq!(s.check(), SatResult::Sat);

        let idx = forall.resource().make_fresh_args();
        let cond = forall.mask().apply_bool(&idx);

        match s.check_assumptions(&[cond]) {
            SatResult::Unsat => false,
            SatResult::Unknown => todo!(),
            SatResult::Sat => true,
        }
    }

    pub fn exactly_equal() {}
    pub fn never_overlap() {}

    pub fn always_contains(&self, large: &Forall, small: &Forall) -> bool {
        if large.resource != small.resource {
            return false;
        }

        // debug_assert_eq!(large_named.typ.tau, small_named.typ.tau);
        let idx = large.resource.make_fresh_args();

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
        let idx = need.resource.make_fresh_args();
        s.assert(&need.mask.apply_bool(&idx));

        match s.check_assumptions(&[l.apply(&idx).eq(&r.apply(&idx)).to_bool().not()]) {
            SatResult::Unsat => {}
            SatResult::Unknown => todo!(),
            SatResult::Sat => {
                panic!("value might be modified")
            }
        }
    }

    // this assumes that the mask is equal, it checks that the values are equal
    pub fn check_eq_part(&self, have: &NewPart, need: &NewPart) {
        // if one side is Once, then expand the other side.
        // repeat untill both sides are Forall, then compare
        let (have, need) = match (have, need) {
            (NewPart::Forall(have), NewPart::Forall(need)) => {
                let idx = have.resource.make_fresh_args();
                let intersect = have.mask.apply(&idx);
                let eq = have.value.apply(&idx).eq(&need.value.apply(&idx));
                assert!(self.is_always_true(intersect.implies(&eq).to_bool()));
                return;
            }
            (NewPart::Partial(have), need) => (need.unfold(&have.args), have),
            (have, NewPart::Partial(need)) => (have.unfold(&need.args), need),
        };

        for key in have.map.keys() {
            self.check_eq_part(&have.map[key], &need.map[key]);
        }
    }

    pub fn get_value(&self, term: &Term) -> Option<u32> {
        let s = self.assume();
        let term = term.as_bv();
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
    pub fn counter_example(
        &self,
        need: Forall,
        have: &[CtxForall],
        scope: &HashMap<String, Nested<Term>>,
    ) -> String {
        let idx = need.resource.make_fresh_args();
        let s = self.assume();
        s.assert(&need.mask.apply_bool(&idx));
        for ctx_forall in have {
            if ctx_forall.have.resource == need.resource {
                s.assert(&ctx_forall.have.mask.apply_bool(&idx).not());
            }
        }
        match s.check() {
            SatResult::Unsat => return "Could not generate a valid counter example".to_owned(),
            SatResult::Unknown => todo!(),
            SatResult::Sat => {}
        }
        let model = s.get_model().unwrap();
        let args: Vec<_> = idx
            .iter()
            .map(|idx| model.eval(idx.as_bv(), true).unwrap().to_string())
            .collect();
        let args = args.join(", ");

        let mut out = String::new();
        format_model(indented(&mut out), model, scope);
        format!(
            "Here is a valid example for which \n\
            the resource does not exist: \n
            resource args are ({args})
            \n{out}"
        )
    }
}

pub fn format_model<F: Write>(
    mut f: F,
    model: Model<'static>,
    scope: &HashMap<String, Nested<Term>>,
) {
    let mut scope = scope.clone();
    scope.iter_mut().for_each(|(_key, val)| val.eval(&model));

    for (name, item) in scope {
        writeln!(f, "{name} = {item:?}").unwrap();
    }
}

impl Nested<Term> {
    pub fn eval(&mut self, model: &Model<'static>) {
        match self {
            Nested::Resource(..) => panic!(),
            Nested::Just(term) => {
                *term = match term {
                    Term::BV(bv) => Term::BV(model.eval(bv, true).unwrap()),
                    Term::Bool(b, _) => Term::bool_bv(model.eval(b, true).unwrap()),
                    Term::Uninterp(u) => Term::Uninterp(model.eval(u, true).unwrap()),
                }
            }
        }
    }
}

impl fmt::Debug for Nested<Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Nested::Resource(..) => panic!(),
            Nested::Just(val) => val.fmt(f),
        }
    }
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
