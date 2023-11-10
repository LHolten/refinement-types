use std::{iter::zip, mem::forget, rc::Rc};

use crate::refinement::Inj;

use super::{
    BoundExpr, Expr, Fun, Lambda, Local, NegTyp, PosTyp, Prop, Sort, SubContext, Term, Thunk, Value,
};

#[derive(Clone)]
pub struct Var {
    args: Vec<(Rc<Term>, Sort)>,
    inner: Rc<PosTyp>,
    rec: Fun<NegTyp>,
}

impl Local<Var> {
    fn infer(&self) -> &(Rc<Term>, Sort) {
        &self.0.args[self.1]
    }
}

pub fn zip_eq<A: IntoIterator, B: IntoIterator>(
    a: A,
    b: B,
) -> impl Iterator<Item = (A::Item, B::Item)>
where
    A::IntoIter: ExactSizeIterator,
    B::IntoIter: ExactSizeIterator,
{
    let (a_iter, b_iter) = (a.into_iter(), b.into_iter());
    assert_eq!(a_iter.len(), b_iter.len());
    zip(a_iter, b_iter)
}

impl Fun<PosTyp> {
    pub fn arrow(self, ret: Fun<PosTyp>) -> Fun<NegTyp> {
        Fun {
            tau: self.tau,
            fun: Rc::new(move |args, heap| NegTyp {
                arg: (self.fun)(args, heap),
                ret: ret.clone(),
            }),
        }
    }
}

impl SubContext {
    pub fn infer_fptr(&self, fptr: &Term) -> &Fun<NegTyp> {
        let mut func_iter = self.funcs.iter();
        let found = func_iter.find(|func| self.is_always_eq(&func.ptr, fptr));
        let found = found.expect("argument must be a function");
        &found.typ
    }

    fn infer_func(&self, func: &Thunk<Var>) -> Fun<NegTyp> {
        match func {
            Thunk::Local(local) => {
                let (fptr, tau) = local.infer();
                assert_eq!(*tau, Sort::Nat);
                self.infer_fptr(fptr).clone()
            }
            Thunk::Builtin(builtin) => builtin.infer(),
        }
    }

    fn calc_args(&self, val: &Value<Var>) -> Vec<Rc<Term>> {
        let mut res = vec![];
        for inj in &val.inj {
            match inj {
                Inj::Just(idx) => {
                    let arg = Rc::new(Term::Nat(*idx));
                    res.push(arg);
                }
                Inj::Var(local) => {
                    let (arg, _tau) = local.infer();
                    res.push(arg.clone())
                }
            }
        }
        res
    }

    // This resolves value determined indices in `p`
    pub fn check_value(&mut self, v: &Value<Var>, p: &Fun<PosTyp>) {
        let p_args = self.calc_args(v);
        let PosTyp = self.with_terms(p, &p_args);
    }

    pub fn spine(&mut self, n: &Fun<NegTyp>, s: &Value<Var>) -> Fun<PosTyp> {
        let n_args = self.calc_args(s);
        let typ = self.with_terms(n, &n_args);
        typ.ret
    }

    pub fn check_expr(mut self, l: &Lambda<Var>, n: &Fun<NegTyp>) {
        let neg = self.extract(n);
        let var = Var {
            args: zip_eq(neg.terms, n.tau.clone()).collect(),
            inner: Rc::new(neg.inner.arg),
            rec: n.clone(),
        };
        let e = l.inst(&var);
        self.check_expr_pos(&e, &neg.inner.ret);
    }

    pub fn check_expr_pos(mut self, e: &Expr<Var>, p: &Fun<PosTyp>) {
        match e {
            Expr::Return(v) => {
                self.check_value(v, p);
                self.check_empty();
            }
            Expr::Let(g, l) => {
                let bound_p = match g {
                    BoundExpr::App(func, s) => {
                        let n = self.infer_func(func);
                        self.spine(&n, s)
                    }
                    BoundExpr::Anno(e, p) => {
                        // as if you call identity
                        self.check_value(e, p);
                        p.clone()
                    }
                };
                self.check_expr(l, &bound_p.arrow(p.clone()))
            }
            Expr::Match(local, pats) => {
                let (term, _tau) = local.infer();
                let (last, pats) = pats.split_last().unwrap();

                for (i, l) in pats.iter().enumerate() {
                    // we want to preserve resources between branches
                    let this = self.clone();
                    let phi = Prop::Eq(term.clone(), Rc::new(Term::Nat(i)));
                    let match_p = this.unroll_prod_univ(phi);
                    this.check_expr(l, &match_p.arrow(p.clone()));
                }

                let phi = Prop::LessEq(Rc::new(Term::Nat(pats.len())), term.clone());
                let match_p = self.unroll_prod_univ(phi);
                self.check_expr(last, &match_p.arrow(p.clone()));
            }
            Expr::Loop(idx, s) => {
                let n = &idx.rec;
                let res = self.spine(n, s);
                self.sub_pos_typ(&res, p);
            }
        }
    }

    pub fn without_alloc(&self) -> Self {
        Self {
            univ: self.univ,
            assume: self.assume.clone(),
            alloc: vec![],
            forall: vec![],
            funcs: vec![],
        }
    }

    pub fn check_empty(mut self) {
        // leaking resources is not allowed
        // TODO: make sure this doesn't leak
        assert!(self.alloc.is_empty(), "can not leak memory");
        assert!(self.forall.is_empty(), "can not leak memory");
        self.assume.clear();
        self.funcs.clear();
        forget(self);
    }
}
