use std::rc::Rc;

use crate::refinement::{Constraint, ContextPart};

use super::{NegTyp, PosTyp, Prop, Term};

#[derive(Clone, Copy)]
pub enum Subst {
    Local(usize),
    Global(usize),
}

impl Subst {
    fn abs(self) -> Self {
        match self {
            Subst::Local(x) => Subst::Local(x + 1),
            Subst::Global(x) => Subst::Global(x),
        }
    }
}

impl Constraint {
    pub fn subst(&self, var: Subst, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            Constraint::True => Constraint::True,
            Constraint::And(w1, w2) => Constraint::And(w1.subst(var, t), w2.subst(var, t)),
            Constraint::Prop(phi) => Constraint::Prop(phi.subst(var, t)),
            Constraint::Context(part, w) => {
                Constraint::Context(part.subst(var, t), w.subst(var, t))
            }
            Constraint::SubNegTyp(n, m) => Constraint::SubNegTyp(n.subst(var, t), m.subst(var, t)),
            Constraint::SubPosTyp(p, q) => Constraint::SubPosTyp(p.subst(var, t), q.subst(var, t)),
            Constraint::Check(e, n) => Constraint::Check(e.clone(), n.subst(var, t)),
        };
        Rc::new(res)
    }
}

impl ContextPart {
    pub fn subst(&self, var: Subst, t: &Rc<Term>) -> Self {
        match self {
            ContextPart::Assume(phi) => ContextPart::Assume(phi.subst(var, t)),
            ContextPart::Free => ContextPart::Free,
        }
    }
}

impl PosTyp {
    pub fn subst(&self, var: Subst, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            PosTyp::Prod(v) => PosTyp::Prod(v.iter().map(|v| v.subst(var, t)).collect()),
            PosTyp::Refined(p, phi) => PosTyp::Refined(p.subst(var, t), phi.subst(var, t)),
            PosTyp::Exists(tau, p) => PosTyp::Exists(*tau, p.subst(var.abs(), t)),
            PosTyp::Thunk(n) => PosTyp::Thunk(n.subst(var, t)),
            PosTyp::Measured(f_alpha, x) => PosTyp::Measured(f_alpha.clone(), x.subst(var, t)),
        };
        Rc::new(res)
    }
}

impl NegTyp {
    pub fn subst(&self, var: Subst, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            NegTyp::Force(p) => NegTyp::Force(p.subst(var, t)),
            NegTyp::Implies(phi, n) => NegTyp::Implies(phi.subst(var, t), n.subst(var, t)),
            NegTyp::Forall(tau, n) => NegTyp::Forall(*tau, n.subst(var.abs(), t)),
            NegTyp::Fun(p, n) => NegTyp::Fun(p.subst(var, t), n.subst(var, t)),
        };
        Rc::new(res)
    }
}

impl Prop {
    pub fn subst(&self, var: Subst, t: &Rc<Term>) -> Rc<Self> {
        let res = match self {
            Prop::Eq(a, b) => Prop::Eq(a.subst(var, t), b.subst(var, t)),
        };
        Rc::new(res)
    }
}

impl Term {
    pub fn subst(self: &Rc<Self>, var: Subst, t: &Rc<Term>) -> Rc<Self> {
        match (self.as_ref(), var) {
            (Self::EVar(x, _), Subst::Global(x_)) if *x == x_ => t.clone(),
            (Self::LVar(x), Subst::Local(x_)) if *x == x_ => t.clone(),
            _ => self.clone(),
        }
    }
}
