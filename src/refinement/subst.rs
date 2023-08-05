use std::rc::Rc;

use super::{NegTyp, PosTyp, Prop, Term};

impl PosTyp {
    pub fn subst(&self, idx: usize, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            PosTyp::Prod(v) => PosTyp::Prod(v.iter().map(|v| v.subst(idx, t)).collect()),
            PosTyp::Refined(p, phi) => PosTyp::Refined(p.subst(idx, t), phi.subst(idx, t)),
            PosTyp::Exists(tau, p) => PosTyp::Exists(*tau, p.subst(idx + 1, t)),
            PosTyp::Thunk(n) => PosTyp::Thunk(n.subst(idx, t)),
            PosTyp::Measured(f_alpha, x) => PosTyp::Measured(f_alpha.clone(), x.subst(idx, t)),
        };
        Rc::new(res)
    }
}

impl NegTyp {
    pub fn subst(&self, idx: usize, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            NegTyp::Force(p) => NegTyp::Force(p.subst(idx, t)),
            NegTyp::Implies(phi, n) => NegTyp::Implies(phi.subst(idx, t), n.subst(idx, t)),
            NegTyp::Forall(tau, n) => NegTyp::Forall(*tau, n.subst(idx + 1, t)),
            NegTyp::Fun(p, n) => NegTyp::Fun(p.subst(idx, t), n.subst(idx, t)),
        };
        Rc::new(res)
    }
}

impl Prop {
    pub fn subst(&self, idx: usize, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            Prop::Eq(a, b) => Prop::Eq(a.subst(idx, t), b.subst(idx, t)),
        };
        Rc::new(res)
    }
}

impl Term {
    pub fn subst(&self, idx: usize, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            Term::LVar(x) => {
                if *x == idx {
                    return t.clone();
                } else {
                    Term::LVar(*x)
                }
            }
            Term::GVar(x) => Term::GVar(*x),
            Term::Prop(phi) => Term::Prop(phi.subst(idx, t)),
            Term::Zero => Term::Zero,
        };
        Rc::new(res)
    }
}
