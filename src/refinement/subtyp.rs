use std::{cmp::max, collections::VecDeque, iter::zip, ops::BitAnd, rc::Rc};

use super::{
    BaseFunctor, Constraint, Context, ContextPart, ExtendedConstraint, NegTyp, PosTyp, ProdFunctor,
    Prop, Sort, Term,
};

type TermSol = VecDeque<Option<Term>>;

pub(super) fn and(iter: impl IntoIterator<Item = ExtendedConstraint>) -> ExtendedConstraint {
    iter.into_iter()
        .fold(ExtendedConstraint::default(), BitAnd::bitand)
}

impl BitAnd for ExtendedConstraint {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let Self { w: w1, r: mut r1 } = self;
        let Self { w: w2, r: r2 } = rhs;
        let new_len = max(r1.len(), r2.len());
        r1.resize_with(new_len, || None);
        for (r1, r2) in zip(&mut r1, r2) {
            *r1 = r1.take().or(r2)
        }
        Self {
            w: Rc::new(Constraint::And(w1, w2)),
            r: r1,
        }
    }
}

impl ExtendedConstraint {
    pub fn and(mut self, rhs: Rc<Constraint>) -> Self {
        self.w = Rc::new(Constraint::And(self.w, rhs));
        self
    }

    pub fn and_prop(self, prop: &Rc<Prop>) -> Self {
        let cons = Rc::new(Constraint::Prop(prop.clone()));
        self.and(cons)
    }

    pub fn and_prop_eq(self, lhs: &Rc<Prop>, rhs: &Rc<Prop>) -> Self {
        let cons = Rc::new(Constraint::PropEq(lhs.clone(), rhs.clone()));
        self.and(cons)
    }

    // uses the found solution for the topmost variable
    pub fn push_down(mut self, tau: &Sort) -> Self {
        let Some(Some(t)) = self.r.pop_front() else {
            panic!()
        };
        let prop = Rc::new(Prop::Eq(Rc::new(Term::LVar(0)), t));
        let implies = Rc::new(Constraint::Implies(prop, self.w));
        self.w = Rc::new(Constraint::Forall(*tau, implies));
        self
    }

    pub fn inst(mut self, t: &Rc<Term>, t_: &Rc<Term>) -> Self {
        let prop = Rc::new(Prop::Eq(t.clone(), t_.clone()));
        self = self.and_prop(&prop);
        if let Term::LVar(x) = t_.as_ref() {
            self.r.resize_with(max(self.r.len(), x + 1), || None);
            self.r[*x] = self.r[*x].take().or_else(|| Some(t.clone()));
        }
        self
    }
}

impl Context {
    pub fn add(self: &Rc<Self>, tau: &Sort) -> Rc<Self> {
        self.extend(vec![ContextPart::Free(*tau)])
    }

    pub fn extend(self: &Rc<Self>, theta: Vec<ContextPart>) -> Rc<Self> {
        let mut next = self.clone();
        for part in theta {
            next = Rc::new(Self::Cons { part, next })
        }
        next
    }

    // can we make this position independent into position independent??
    pub fn extract_neg(self: &Rc<Self>, n: &Rc<NegTyp>) -> (Rc<NegTyp>, Vec<ContextPart>) {
        match n.as_ref() {
            NegTyp::Implies(phi, n) => {
                let (n, mut theta) = self.extract_neg(n);
                theta.push(ContextPart::Assume(phi.clone()));
                (n, theta)
            }
            NegTyp::Forall(tau, n) => {
                let gvar = Rc::new(Term::GVar(self.len()));
                let (n, mut theta) = self.add(tau).extract_neg(n);
                theta.push(ContextPart::Free(*tau));
                (n.subst(0, &gvar), theta)
            }
            NegTyp::Fun(p, n) => {
                let (p, mut theta_p) = self.extract_pos(p);
                let (n, theta_n) = self.extract_neg(n);
                theta_p.extend(theta_n);
                (Rc::new(NegTyp::Fun(p, n)), theta_p)
            }
            _ => (n.clone(), vec![]),
        }
    }

    pub fn extract_pos(self: &Rc<Self>, p: &Rc<PosTyp>) -> (Rc<PosTyp>, Vec<ContextPart>) {
        match p.as_ref() {
            PosTyp::Refined(p, phi) => {
                let (p, mut theta) = self.extract_pos(p);
                theta.push(ContextPart::Assume(phi.clone()));
                (p, theta)
            }
            PosTyp::Exists(tau, p) => {
                let gvar = Rc::new(Term::GVar(self.len()));
                let (p, mut theta) = self.add(tau).extract_pos(p);
                theta.push(ContextPart::Free(*tau));
                (p.subst(0, &gvar), theta)
            }
            PosTyp::Prod(p) => {
                let mut theta1 = vec![];
                let mut p1 = vec![];
                for p2 in p {
                    let (p2, theta2) = self.extract_pos(p2);
                    p1.push(p2);
                    theta1.extend(theta2);
                }
                (Rc::new(PosTyp::Prod(p1)), theta1)
            }
            _ => (p.clone(), vec![]),
        }
    }

    pub fn sub_base_functor(
        self: &Rc<Self>,
        f: &BaseFunctor,
        g: &BaseFunctor,
    ) -> ExtendedConstraint {
        match (f, g) {
            (BaseFunctor::Pos(p), BaseFunctor::Pos(q)) => self.sub_pos_typ(p, q),
            (BaseFunctor::Id, BaseFunctor::Id) => ExtendedConstraint::default(),
            _ => panic!(),
        }
    }

    pub fn sub_prod_functor(
        self: &Rc<Self>,
        f: &ProdFunctor,
        g: &ProdFunctor,
    ) -> ExtendedConstraint {
        let mut res = ExtendedConstraint::default();
        assert_eq!(f.prod.len(), g.prod.len());
        for (x, y) in zip(&f.prod, &g.prod) {
            res = res & self.sub_base_functor(x, y)
        }
        res
    }

    // `p` is ground, solves all "value determined" indices in `q`
    // `p` must also be position independent
    pub fn sub_pos_typ(self: &Rc<Self>, p: &PosTyp, q: &PosTyp) -> ExtendedConstraint {
        match (p, q) {
            (PosTyp::Prod(p), PosTyp::Prod(q)) => {
                let iter = zip(p, q).map(|(p, q)| self.sub_pos_typ(p, q));
                and(iter)
            }
            (p, PosTyp::Refined(q, phi)) => {
                let w = self.sub_pos_typ(p, q);
                w.and_prop(phi)
            }
            (p, PosTyp::Exists(tau, q)) => {
                let w = self.add(tau).sub_pos_typ(p, q);
                w.push_down(tau)
            }
            (PosTyp::Thunk(n), PosTyp::Thunk(m)) => {
                let (m, theta) = self.extract_neg(m);
                let w = Rc::new(Constraint::SubNegTyp(n.clone(), m));
                w.extend(&theta)
            }
            (PosTyp::Measured(f_alpha, t), PosTyp::Measured(g_alpha, t_)) => {
                assert_eq!(f_alpha.len(), g_alpha.len());
                let iter = zip(f_alpha, g_alpha).map(|(f_alpha, g_alpha)| {
                    assert!(f_alpha.1 == g_alpha.1);
                    self.sub_prod_functor(&f_alpha.0, &g_alpha.0)
                });
                let w = and(iter);
                w.inst(t, t_)
            }
            _ => panic!(),
        }
    }

    // `m` must be position independent
    // value determined instances in `n` are resolved
    pub fn sub_neg_type(self: &Rc<Self>, n: &NegTyp, m: &NegTyp) -> ExtendedConstraint {
        match (n, m) {
            (NegTyp::Force(p), NegTyp::Force(q)) => {
                // `p` might have existential variables refering to our scope
                // we remove a bunch of binders and add them in the constraint
                // this keeps the existential variables correctly bound, because
                // we will add the existential variables to the the context when they are solved.
                // we do not update the variables that were bound by `theta`
                // Luckily all vars start out as LVar, so this is fine!
                let (p, theta) = self.extract_pos(p);
                let w = Rc::new(Constraint::SubPosTyp(p, q.clone()));
                w.extend(&theta)
            }
            (NegTyp::Implies(phi, n), m) => {
                let w = self.sub_neg_type(n, m);
                w.and_prop(phi)
            }
            (NegTyp::Forall(tau, n), m) => {
                let w = self.add(tau).sub_neg_type(n, m);
                w.push_down(tau)
            }
            (NegTyp::Fun(p, n), NegTyp::Fun(q, m)) => {
                // arguments are swapped! (fun is contravariant in the argument)
                let w1 = self.sub_pos_typ(q, p);
                let w2 = self.sub_neg_type(n, m);
                w1 & w2
            }
            _ => panic!(),
        }
    }
}

impl Constraint {
    pub fn extend(mut self: Rc<Self>, theta: &[ContextPart]) -> ExtendedConstraint {
        for part in theta {
            let res = match part {
                ContextPart::Assume(phi) => Self::Implies(phi.clone(), self),
                ContextPart::Free(tau) => Self::Forall(*tau, self),
            };
            self = Rc::new(res)
        }
        ExtendedConstraint {
            w: self,
            r: VecDeque::new(),
        }
    }
}
