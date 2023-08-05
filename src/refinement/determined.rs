use std::{cmp::max, collections::VecDeque, iter::zip, rc::Rc};

use crate::refinement::{BaseFunctor, ContextPart};

use super::{Context, NegTyp, PosTyp, ProdFunctor, Prop, Sort, Term};

pub fn or(mut r1: VecDeque<bool>, mut r2: VecDeque<bool>) -> VecDeque<bool> {
    let total_len = max(r1.len(), r2.len());
    r1.resize(total_len, false);
    r2.resize(total_len, false);
    zip(r1, r2).map(|(x, y)| x | y).collect()
}

impl Context {
    pub fn infer_prop(&self, phi: &Prop) -> Sort {
        match phi {
            Prop::Eq(a, b) => {
                assert_eq!(self.infer_term(a), self.infer_term(b));
            }
        }
        Sort::Bool
    }

    pub fn infer_term(&self, t: &Term) -> Sort {
        match t {
            Term::LVar(b) => self.get(b),
            Term::Prop(phi) => self.infer_prop(phi),
            Term::Zero => Sort::Nat,
        }
    }

    pub fn get(&self, b: &usize) -> Sort {
        fn next_sort(mut res: &Context) -> (Sort, &Context) {
            loop {
                let Context::Cons { part, next } = res else {
                    panic!()
                };
                if let ContextPart::Free(tau) = part {
                    return (*tau, next.as_ref());
                }
                res = next.as_ref();
            }
        }

        let mut res = self;
        for _ in 0..*b {
            (_, res) = next_sort(res);
        }
        let (tau, _) = next_sort(res);
        tau
    }

    // this needs to check that every index is used and other things
    // the returned value is a bitset indicating which variables were used
    // for now the variable index is the VecDeque index
    pub fn value_determined_pos(self: &Rc<Self>, p: &PosTyp) -> VecDeque<bool> {
        match p {
            PosTyp::Prod(p) => {
                let mut r = VecDeque::new();
                for p in p {
                    r = or(r, self.value_determined_pos(p))
                }
                r
            }
            PosTyp::Refined(p, phi) => {
                let Sort::Bool = self.infer_prop(phi) else {
                    panic!()
                };
                self.value_determined_pos(p)
            }
            PosTyp::Exists(tau, p) => {
                let mut r = self.add(tau).value_determined_pos(p);
                let Some(true) = r.pop_front() else { panic!() };
                r
            }
            PosTyp::Thunk(n) => {
                let _ = self.value_determined_neg(n);
                VecDeque::new()
            }
            PosTyp::Measured(f_alpha, t) => {
                let tau = self.infer_term(t);
                for (i, (_g, beta)) in f_alpha.iter().enumerate() {
                    let p = self.unroll_prod(f_alpha, i, t);
                    let (_, theta) = self.extract_pos(&p);
                    // TODO: maybe remove the outer scope so that beta can not refer to it?
                    assert_eq!(tau, self.extend(theta).infer_term(beta))
                }

                // we will just assume that there is at least one variant
                let Some(((f, _), f_alpha_)) = f_alpha.split_first() else {
                    panic!()
                };
                let mut r = self.value_determined_functor(f);
                for (f, _) in f_alpha_ {
                    let v2 = self.value_determined_functor(f);
                    r = zip(r, v2).map(|(x, y)| x & y).collect();
                }

                if let Term::LVar(b) = t.as_ref() {
                    // if the term is just a variable, then it is value determined!
                    r.resize(b + 1, false);
                    r[*b] = true;
                }
                r
            }
        }
    }

    pub fn value_determined_neg(self: &Rc<Self>, n: &NegTyp) -> VecDeque<bool> {
        match n {
            NegTyp::Force(p) => {
                let _ = self.value_determined_pos(p);
                VecDeque::new()
            }
            NegTyp::Implies(phi, n) => {
                let Sort::Bool = self.infer_prop(phi) else {
                    panic!()
                };
                self.value_determined_neg(n)
            }
            NegTyp::Forall(tau, n) => {
                let mut r = self.add(tau).value_determined_neg(n);
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

    pub fn value_determined_functor(self: &Rc<Self>, f: &ProdFunctor) -> VecDeque<bool> {
        let mut r = VecDeque::new();
        for f in &f.prod {
            match f {
                BaseFunctor::Pos(p) => {
                    r = or(r, self.value_determined_pos(p));
                }
                BaseFunctor::Id => {}
            }
        }
        r
    }
}
