use std::{iter::zip, rc::Rc};

use crate::refinement::VarContext;

use super::{
    subtyp::and, BoundExpr, Constraint, ContextPart, Expr, ExtendedConstraint, FullContext, Head,
    NegTyp, PosTyp, Prop, Sort, Term, Value,
};

// Value, Head, Expr and BoundExpr are always position independent
// "position independent" only refers to sort indices
impl FullContext {
    // TODO: This should probably make LVars that refer to the context into GVars.
    // That is the only way to make it relocatable
    // I don't know if we can do this by wrapping..
    pub fn add_pos(&self, p: &Rc<PosTyp>) -> Self {
        let (p, theta) = self.ctx.extract_pos(p);
        let mut this = self.extend(theta);
        this.var = Rc::new(VarContext::Cons {
            typ: p.clone(),
            next: this.var,
        });
        this
    }

    // the returned type is position independent
    pub fn get_pos(&self, x: &usize, proj: &[usize]) -> &Rc<PosTyp> {
        let mut res = &self.var;
        for _ in 0..*x {
            let VarContext::Cons { typ: _, next } = res.as_ref() else {
                panic!()
            };
            res = next;
        }
        let VarContext::Cons { typ, next: _ } = res.as_ref() else {
            panic!()
        };
        let mut p = typ;
        for proj in proj {
            let PosTyp::Prod(v) = typ.as_ref() else {
                panic!()
            };
            p = &v[*proj];
        }
        p
    }

    pub fn add(&self, tau: &Sort) -> Self {
        let mut this = self.clone();
        this.ctx = this.ctx.add(tau);
        this
    }

    pub fn extend(&self, theta: Vec<ContextPart>) -> Self {
        let mut this = self.clone();
        this.ctx = this.ctx.extend(theta);
        this
    }

    // This resolves value determined indices in `p`
    // value determined indices are always LVar?
    pub fn check_value(&self, v: &Value, p: &PosTyp) -> ExtendedConstraint {
        match p {
            PosTyp::Refined(p, phi) => {
                let xi = self.check_value(v, p);
                xi.and_prop(phi)
            }
            PosTyp::Exists(tau, p) => {
                let extended = self.add(tau);
                let xi = extended.check_value(v, p);
                xi.push_down(tau)
            }
            _ => match v {
                Value::Var(x, proj) => {
                    let q = self.get_pos(x, proj);
                    self.ctx.sub_pos_typ(q, p)
                }
                Value::Tuple(v) => {
                    let PosTyp::Prod(p) = p else { panic!() };
                    let iter = zip(v, p).map(|(v, p)| self.check_value(v, p));
                    and(iter)
                }
                Value::Thunk(e) => {
                    let PosTyp::Thunk(n) = p else { panic!() };
                    Rc::new(Constraint::Check(e.clone(), n.clone())).extend(&[])
                }
                Value::Inj(i, v) => {
                    let PosTyp::Measured(f_alpha, t) = p else {
                        panic!()
                    };
                    let p = self.unroll_prod(f_alpha, *i, t);
                    self.check_value(v, &p)
                }
            },
        }
    }

    // This resolves value determined indices in `n`
    // if `n` is position independent, then the output is also position independent
    pub fn spine(&self, n: &NegTyp, s: &[Value]) -> (Rc<PosTyp>, ExtendedConstraint) {
        match n {
            NegTyp::Force(p) => {
                let [] = s else { panic!() };
                (p.clone(), ExtendedConstraint::default())
            }
            NegTyp::Implies(phi, n) => {
                let (p, xi) = self.spine(n, s);
                (p, xi.and_prop(phi))
            }
            NegTyp::Forall(tau, n) => {
                let extended = self.add(tau);
                let (p, xi) = extended.spine(n, s);
                // TODO: somehow apply `t` to `p`??
                // is the following code correct?
                let t = xi.r.front().unwrap().as_ref().unwrap();
                let prop = Rc::new(Prop::Eq(Rc::new(Term::LVar(0)), t.clone()));
                let p = PosTyp::Exists(*tau, Rc::new(PosTyp::Refined(p, prop)));
                (Rc::new(p), xi.push_down(tau))
            }
            NegTyp::Fun(q, n) => {
                let [v, s @ ..] = s else { panic!() };
                let xi1 = self.check_value(v, q);
                let (p, xi2) = self.spine(n, s);
                (p, xi1 & xi2)
            }
        }
    }

    // the result of infer_head is position independent
    pub fn infer_head(&self, h: &Head) -> Rc<PosTyp> {
        match h {
            Head::Var(x, proj) => {
                let p = self.get_pos(x, proj);
                p.clone()
            }
            Head::Anno(v, p) => {
                // TODO: check that `p` is a type
                let xi = self.check_value(v, p);
                self.verify(&xi.w);
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
                self.verify(&xi.w);
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
        let (n, theta) = self.ctx.extract_neg(n);
        let this = self.extend(theta);
        match e {
            Expr::Return(v) => {
                let NegTyp::Force(p) = n.as_ref() else {
                    panic!()
                };
                let xi = this.check_value(v, p);
                self.verify(&xi.w);
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
