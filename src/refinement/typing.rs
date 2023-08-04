use std::{iter::zip, rc::Rc};

use super::{
    BoundExpr, Constraint, Context, ContextPart, Expr, FullContext, Head, NegTyp, PosTyp, Prop,
    TConstraint, Term, Value,
};

pub(super) fn t_and(iter: impl Iterator<Item = Rc<TConstraint>>) -> TConstraint {
    let xi = TConstraint::Cons(Rc::new(Constraint::True));
    iter.fold(xi, |xi, xi_n| TConstraint::And(Rc::new(xi), xi_n))
}

// Value, Head, Expr and BoundExpr are always position independent
// "position independent" only refers to sort indices
impl Context {
    // This should probably make LVars that refer to the context into GVars.
    // That is the only way to make it relocatable
    // I don't know if we can do this by wrapping..
    pub fn add_pos(&self, p: &Rc<PosTyp>) -> Self {
        let (p, theta) = self.extract_pos(p);
        let this = self.extend(theta);
        todo!()
    }

    // the returned type is position independent
    pub fn get_pos(&self, x: &usize, proj: &[usize]) -> Option<&Rc<PosTyp>> {
        // match self {
        //     Context::Empty => panic!(),
        //     Context::Cons { part, next } => {
        //         let res = next.get_pos(x, proj);
        //     }
        // }

        // for proj in proj {
        //     let PosTyp::Prod(a, b) = p.as_ref() else { panic!() };
        //     p = [a, b][*proj];
        // }
        // p.clone()
        todo!()
    }

    // This resolves value determined indices in `p`
    pub fn check_value(&self, v: &Value, p: &PosTyp) -> Rc<TConstraint> {
        let res = match p {
            PosTyp::Refined(p, phi) => {
                let xi2 = self.check_value(v, p);
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

    // This resolves value determined indices in `n`
    // if `n` is position independent, then the output is also position independent
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
                // is the following code correct?
                let prop = Rc::new(Prop::Eq(Rc::new(Term::LVar(0)), t.clone()));
                let p = PosTyp::Exists(*tau, Rc::new(PosTyp::Refined(p, prop)));
                (Rc::new(p), xi.apply(t))
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

    // the result of infer_head is position independent
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

    // the result is position independent
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

    // can we make sure than `n` is always position independent????
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
                this.add_pos(&p).check_expr(e, &n)
            }
            Expr::Match(h, pats) => {
                let p = self.infer_head(h);
                let PosTyp::Measured(f_alpha, t) = p.as_ref() else {
                    panic!()
                };
                assert_eq!(pats.len(), f_alpha.len());
                for (i, e) in pats.iter().enumerate() {
                    let p = self.unroll_prod(f_alpha, i, t);
                    this.add_pos(&p).check_expr(e, &n);
                }
            }
            Expr::Lambda(e) => {
                let NegTyp::Fun(p, n) = n.as_ref() else {
                    panic!()
                };
                this.add_pos(p).check_expr(e, n)
            }
        }
    }
}
