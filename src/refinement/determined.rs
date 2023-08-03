use std::{cmp::max, collections::VecDeque, iter::zip};

use super::{Context, NegTyp, PosTyp, Prop, Sort, SumFunctor, Term};

pub fn or(mut r1: VecDeque<bool>, mut r2: VecDeque<bool>) -> VecDeque<bool> {
    let total_len = max(r1.len(), r2.len());
    r1.resize(total_len, false);
    r2.resize(total_len, false);
    zip(r1, r2).map(|(x, y)| x | y).collect()
}

impl Context<'_> {
    pub fn infer_prop(&self, phi: &Prop) -> Sort {
        todo!()
    }

    pub fn infer_term(&self, t: &Term) -> Sort {
        match t {
            Term::Var(b) => self.get(b),
            Term::Prop(phi) => self.infer_prop(phi),
        }
    }

    pub fn get(&self, b: &usize) -> Sort {
        todo!()
    }

    // this needs to check that every index is used and other things
    // the returned value is a bitset indicating which variables were used
    // for now the variable index is the VecDeque index
    pub fn value_determined_pos(&self, p: &PosTyp) -> VecDeque<bool> {
        match p {
            PosTyp::Prod(p) => {
                let mut r = VecDeque::new();
                for p in p {
                    r = or(r, self.value_determined_pos(p))
                }
                r
            }
            PosTyp::Sum(p1, p2) => {
                let r1 = self.value_determined_pos(p1);
                let r2 = self.value_determined_pos(p2);
                zip(r1, r2).map(|(x, y)| x & y).collect()
            }
            PosTyp::Refined(p, phi) => {
                let Sort::Bool = self.infer_prop(phi) else { panic!() };
                self.value_determined_pos(p)
            }
            PosTyp::Exists(tau, p) => {
                let mut r = self.forall(tau).value_determined_pos(p);
                let Some(true) = r.pop_front() else { panic!() };
                r
            }
            PosTyp::Thunk(n) => {
                let _ = self.value_determined_neg(n);
                VecDeque::new()
            }
            PosTyp::Measured(f, alpha, t) => {
                let mut r = self.value_determined_functor(f);
                if let Term::Var(b) = t.as_ref() {
                    // if the term is just a variable, then it is value determined!
                    r.resize(b + 1, false);
                    r[*b] = true;
                }
                let tau = self.infer_term(t);
                // TODO: check the algebra alpha has type f(tau) -> tau
                r
            }
        }
    }

    pub fn value_determined_neg(&self, n: &NegTyp) -> VecDeque<bool> {
        match n {
            NegTyp::Force(p) => {
                let _ = self.value_determined_pos(p);
                VecDeque::new()
            }
            NegTyp::Implies(phi, n) => {
                let Sort::Bool = self.infer_prop(phi) else { panic!() };
                self.value_determined_neg(n)
            }
            NegTyp::Forall(tau, n) => {
                let mut r = self.forall(tau).value_determined_neg(n);
                let Some(true) = r.pop_front() else { panic!() };
                r
            }
            NegTyp::Fun(p, n) => {
                let r1 = self.value_determined_pos(p);
                let r2 = self.value_determined_neg(n);
                or(r1, r2)
            }
        }
    }

    pub fn value_determined_functor(&self, f: &SumFunctor) -> VecDeque<bool> {
        todo!()
    }
}
