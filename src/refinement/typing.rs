use std::rc::Rc;

use super::{
    BoundExpr, Constraint, Context, ContextPart, Expr, Head, NegTyp, PosTyp, TConstraint, Value,
};

impl<'a> Context<'a> {
    pub fn add_pos(&self, p: &Rc<PosTyp>) -> Self {
        todo!()
    }

    pub fn get_pos(&self, x: &usize) -> Option<&Rc<PosTyp>> {
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
                let Some(t) = extended.get_exists(0) else { panic!() };
                xi.apply(t)
            }
            _ => match v {
                Value::Var(x) => {
                    let Some(q) = self.get_pos(x) else { panic!() };
                    let w = self.sub_pos_typ(q, p);
                    TConstraint::Cons(w)
                }
                Value::Pair(v1, v2) => {
                    let PosTyp::Prod(p1, p2)= p else { panic!()};
                    let xi1 = self.check_value(v1, p1);
                    let xi2 = self.check_value(v2, p2);
                    TConstraint::And(xi1, xi2)
                }
                Value::Thunk(e) => {
                    let PosTyp::Thunk(n) = p else { panic!() };
                    TConstraint::Check(e.clone(), n.clone())
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
                let Some(t) = extended.get_exists(0) else { panic!() };
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
            Head::Var(x) => {
                let Some(p) = self.get_pos(x) else { panic!() };
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
                let PosTyp::Thunk(n) = temp.as_ref() else { panic!() };
                let (p, xi) = self.spine(n, s);
                self.verify_t(&xi);
                p
            }
            BoundExpr::Anno(e, p) => {
                // TODO check that `p` is a type
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
                let NegTyp::Force(p) = n.as_ref() else { panic!() };
                this.check_value(v, p);
            }
            Expr::Let(g, e) => {
                let p = this.infer_bound_expr(g);
                let (p, theta) = this.extract_pos(&p);
                let this = this.extend(theta);
                let this = this.add_pos(&p);
                this.check_expr(e, &n)
            }
            Expr::Match(_, _) => todo!(),
            Expr::Lambda(e) => {
                let NegTyp::Fun(p, n) = n.as_ref() else { panic!() };
                let this = this.add_pos(p);
                this.check_expr(e, n)
            }
        }
    }

    pub fn extend(&self, theta: Vec<ContextPart>) -> Self {
        todo!()
    }
}
