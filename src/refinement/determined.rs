use std::{cmp::max, iter::zip, rc::Rc};

use crate::refinement::{BaseFunctor, SubContext};

use super::{InnerTerm, NegTyp, PosTyp, ProdFunctor, Prop, Sort, Term};

pub fn or(mut r1: Vec<bool>, mut r2: Vec<bool>) -> Vec<bool> {
    let total_len = max(r1.len(), r2.len());
    r1.resize(total_len, false);
    r2.resize(total_len, false);
    zip(r1, r2).map(|(x, y)| x | y).collect()
}

impl SubContext {
    pub fn infer_prop(&self, phi: &Prop) -> Sort {
        match phi {
            Prop::Eq(a, b) => {
                assert_eq!(self.infer_term(a), self.infer_term(b));
            }
        }
        Sort::Bool
    }

    pub fn infer_term(&self, t: &Term) -> Sort {
        match *t.borrow() {
            InnerTerm::UVar(_, s) => s,
            InnerTerm::EVar(_, s) => s,
            InnerTerm::Prop(ref phi) => self.infer_prop(phi),
            InnerTerm::Zero => Sort::Nat,
        }
    }

    pub fn new_uvar(&self, tau: &Sort) -> (Self, Rc<Term>) {
        let uvar = InnerTerm::UVar(self.univ, *tau).share();
        let this = Self {
            exis: self.exis,
            univ: self.univ + 1,
            assume: self.assume.clone(),
        };
        (this, uvar)
    }

    pub fn new_evar(&self, tau: &Sort) -> (Self, Rc<Term>) {
        let evar = InnerTerm::EVar(self.exis, *tau).share();
        let this = Self {
            exis: self.exis + 1,
            univ: self.univ,
            assume: self.assume.clone(),
        };
        (this, evar)
    }

    // // this needs to check that every index is used and other things
    // // the returned value is a bitset indicating which variables were used
    // // for now the variable index is the VecDeque index
    // pub fn value_determined_pos(&self, p: &PosTyp) -> Vec<bool> {
    //     match p {
    //         PosTyp::Prod(p) => {
    //             let mut r = Vec::new();
    //             for p in p {
    //                 r = or(r, self.value_determined_pos(p))
    //             }
    //             r
    //         }
    //         PosTyp::Refined(p, phi) => {
    //             let Sort::Bool = self.infer_prop(phi) else {
    //                 panic!()
    //             };
    //             self.value_determined_pos(p)
    //         }
    //         PosTyp::Exists(p) => {
    //             let (this, evar) = self.new_evar(&p.tau);
    //             let p = (p.fun)(&evar);
    //             let r = this.value_determined_pos(&p);
    //             let Some(true) = r.get(self.exis) else {
    //                 panic!()
    //             };
    //             r
    //         }
    //         PosTyp::Thunk(n) => {
    //             let _ = self.value_determined_neg(n);
    //             Vec::new()
    //         }
    //         PosTyp::Measured(f_alpha, t) => {
    //             let tau = self.infer_term(t);
    //             for (i, (_g, beta)) in f_alpha.iter().enumerate() {
    //                 let (p, _) = self.unroll_prod(f_alpha, i, t);
    //                 let (_, theta) = self.extract_pos(&p);
    //                 // TODO: maybe remove the outer scope so that beta can not refer to it?
    //                 assert_eq!(tau, self.extend_univ(theta).infer_term(beta))
    //             }

    //             // we will just assume that there is at least one variant
    //             let Some(((f, _), f_alpha_)) = f_alpha.split_first() else {
    //                 panic!()
    //             };
    //             let mut r = self.value_determined_functor(f);
    //             for (f, _) in f_alpha_ {
    //                 let v2 = self.value_determined_functor(f);
    //                 r = zip(r, v2).map(|(x, y)| x & y).collect();
    //             }

    //             if let InnerTerm::EVar(x, _) = *t.borrow() {
    //                 // if the term is just a variable, then it is value determined!
    //                 r.resize(x + 1, false);
    //                 r[x] = true;
    //             }
    //             r
    //         }
    //     }
    // }

    // pub fn value_determined_neg(&self, n: &NegTyp) -> Vec<bool> {
    //     match n {
    //         NegTyp::Force(p) => {
    //             let _ = self.value_determined_pos(p);
    //             Vec::new()
    //         }
    //         NegTyp::Implies(phi, n) => {
    //             let Sort::Bool = self.infer_prop(phi) else {
    //                 panic!()
    //             };
    //             self.value_determined_neg(n)
    //         }
    //         NegTyp::Forall(n) => {
    //             let (this, evar) = self.new_evar(&n.tau);
    //             let n = (n.fun)(&evar);
    //             let r = this.value_determined_neg(&n);
    //             let Some(true) = r.get(self.exis) else {
    //                 panic!()
    //             };
    //             r
    //         }
    //         NegTyp::Fun(p, n) => {
    //             let r1 = self.value_determined_pos(p);
    //             let r2 = self.value_determined_neg(n);
    //             or(r1, r2)
    //         }
    //     }
    // }

    // pub fn value_determined_functor(&self, f: &ProdFunctor) -> Vec<bool> {
    //     let mut r = Vec::new();
    //     for f in &f.prod {
    //         match f {
    //             BaseFunctor::Pos(p) => {
    //                 r = or(r, self.value_determined_pos(p));
    //             }
    //             BaseFunctor::Id => {}
    //         }
    //     }
    //     r
    // }
}
