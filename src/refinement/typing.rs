use std::{iter::zip, rc::Rc};

use super::{
    BoundExpr, Constraint, Context, ContextPart, Expr, Head, NegTyp, PosTyp, TConstraint, Value,
};

pub(super) fn t_and(iter: impl Iterator<Item = Rc<TConstraint>>) -> TConstraint {
    let xi = TConstraint::Cons(Rc::new(Constraint::True));
    iter.fold(xi, |xi, xi_n| TConstraint::And(Rc::new(xi), xi_n))
}

impl<'a> Context<'a> {
    pub fn add_pos(&self, p: &Rc<PosTyp>) -> Self {
        todo!()
    }

    pub fn get_pos(&self, x: &usize, proj: &[usize]) -> Option<&Rc<PosTyp>> {
        // for proj in proj {
        //     let PosTyp::Prod(a, b) = p.as_ref() else { panic!() };
        //     p = [a, b][*proj];
        // }
        // p.clone()
        todo!()
    }

    // This resolves existential values from the context in `p`
    pub fn check_value(&'a self, v: &Value, p: &PosTyp) -> Rc<TConstraint> {
        let res = match p {
            PosTyp::Refined(p, phi) => {
                let xi2 = self.check_value(v, p);
                self.inst(phi);
                let xi1 = Rc::new(TConstraint::Cons(Rc::new(Constraint::Prop(phi.clone()))));
                TConstraint::And(xi1, xi2)
            }
            PosTyp::Exists(tau, p) => {
                let extended = self.exists(tau);
                let xi = extended.check_value(v, p);
                let Some(t) = extended.get_exists(0) else {
                    panic!()
                };
                xi.apply(t)
            }
            _ => match v {
                Value::Var(x, proj) => {
                    let Some(q) = self.get_pos(x, proj) else {
                        panic!()
                    };
                    let w = self.sub_pos_typ(q, p);
                    TConstraint::Cons(w)
                }
                Value::Tuple(v) => {
                    let PosTyp::Prod(p) = p else { panic!() };
                    let iter = zip(v, p).map(|(v, p)| self.check_value(v, p));
                    t_and(iter)
                }
                Value::Thunk(e) => {
                    let PosTyp::Thunk(n) = p else { panic!() };
                    TConstraint::Check(e.clone(), n.clone())
                }
                Value::Inj(i, v) => {
                    let PosTyp::Measured(f_alpha, t) = p else {
                        panic!()
                    };
                    let p = self.unroll_prod(f_alpha, *i, t);
                    return self.check_value(v, &p);
                }
            },
        };
        Rc::new(res)
    }

    // This resolves existential values from the context in `n`
    pub fn spine(&self, n: &NegTyp, s: &[Value]) -> (Rc<PosTyp>, Rc<TConstraint>) {
        let (p, xi) = match n {
            NegTyp::Force(p) => {
                let [] = s else { panic!() };
                (p.clone(), TConstraint::Cons(Rc::new(Constraint::True)))
            }
            NegTyp::Implies(phi, n) => {
                let (p, xi2) = self.spine(n, s);
                let xi1 = Rc::new(TConstraint::Cons(Rc::new(Constraint::Prop(phi.clone()))));
                (p, TConstraint::And(xi1, xi2))
            }
            NegTyp::Forall(tau, n) => {
                let extended = self.exists(tau);
                let (p, xi) = extended.spine(n, s);
                let Some(t) = extended.get_exists(0) else {
                    panic!()
                };
                // TODO: somehow apply `t` to `p`??
                (p, xi.apply(t))
            }
            NegTyp::Fun(q, n) => {
                let [v, s @ ..] = s else { panic!() };
                let xi1 = self.check_value(v, q);
                let (p, xi2) = self.spine(n, s);
                (p, TConstraint::And(xi1, xi2))
            }
        };
        (p, Rc::new(xi))
    }

    pub fn infer_head(&self, h: &Head) -> Rc<PosTyp> {
        match h {
            Head::Var(x, proj) => {
                let Some(p) = self.get_pos(x, proj) else {
                    panic!()
                };
                p.clone()
            }
            Head::Anno(v, p) => {
                // TODO: check that `p` is a type
                let xi = self.check_value(v, p);
                self.verify_t(&xi);
                p.clone()
            }
        }
    }

    pub fn infer_bound_expr(&self, g: &BoundExpr) -> Rc<PosTyp> {
        match g {
            BoundExpr::App(h, s) => {
                let temp = self.infer_head(h);
                let PosTyp::Thunk(n) = temp.as_ref() else {
                    panic!()
                };
                let (p, xi) = self.spine(n, s);
                self.verify_t(&xi);
                p
            }
            BoundExpr::Anno(e, p) => {
                // TODO: check that `p` is a type
                self.check_expr(e, &Rc::new(NegTyp::Force(p.clone())));
                p.clone()
            }
        }
    }

    pub fn check_expr(&self, e: &Expr, n: &Rc<NegTyp>) {
        let (n, theta) = self.extract_neg(n);
        let this = self.extend(theta);
        match e {
            Expr::Return(v) => {
                let NegTyp::Force(p) = n.as_ref() else {
                    panic!()
                };
                this.check_value(v, p);
            }
            Expr::Let(g, e) => {
                let p = this.infer_bound_expr(g);
                let (p, theta) = this.extract_pos(&p);
                let this = this.extend(theta);
                let this = this.add_pos(&p);
                this.check_expr(e, &n)
            }
            Expr::Match(h, pats) => {
                let p = self.infer_head(h);
                let PosTyp::Measured(f_alpha, t) = p.as_ref() else {
                    panic!()
                };
                assert_eq!(pats.len(), f_alpha.len());
                for (i, e) in pats.iter().enumerate() {
                    let p = self.unroll_prod(f_alpha, i, t);
                    let (p, theta) = self.extract_pos(&p);
                    let this = self.extend(theta).add_pos(&p);
                    this.check_expr(e, &n);
                }
            }
            Expr::Lambda(e) => {
                let NegTyp::Fun(p, n) = n.as_ref() else {
                    panic!()
                };
                let this = this.add_pos(p);
                this.check_expr(e, n)
            }
        }
    }

    pub fn extend(&self, theta: Vec<ContextPart>) -> Self {
        todo!()
    }
}
