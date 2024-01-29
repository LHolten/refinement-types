use std::{
    collections::HashMap,
    fmt::Debug,
    iter::zip,
    rc::{Rc, Weak},
};

use miette::{Diagnostic, LabeledSpan, SourceSpan};
use thiserror::Error;

use crate::{desugar::Desugar, error::AppendLabels, parse, refinement::Free};

use super::{
    term::Term, Expr, Fun, Lambda, NegTyp, PosTyp, Spanned, SubContext, Thunk, Val, Value,
};

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
            span: ret.span,
            fun: Rc::new(move |args, heap| {
                Ok(NegTyp {
                    arg: (self.fun)(args, heap)?,
                    ret: ret.clone(),
                })
            }),
        }
    }
}

impl Val for Term {
    type Func = Fun<NegTyp>;
    fn make(
        this: &Desugar<Self>,
        _lamb: &Weak<Lambda<Self>>,
        typ: &parse::types::NegTyp,
    ) -> Self::Func {
        let mut types = this.types.clone();
        types.terms.extend(this.vars.clone());
        types.convert_neg(typ.clone())
    }
}

impl SubContext {
    fn infer_func(&self, func: &Thunk<Term>) -> Fun<NegTyp> {
        match func {
            Thunk::Local(local) => local.clone(),
            Thunk::Builtin(builtin) => builtin.infer(),
        }
    }

    fn calc_args(&mut self, val: &Value<Term>) -> Vec<Term> {
        self.scope = val.scope.clone();

        let mut res = vec![];
        for inj in &val.inj {
            res.push(self.check_free(inj))
        }
        res
    }

    pub fn check_free(&self, free: &Free<Term>) -> Term {
        match free {
            Free::Just(idx, size) => Term::nat(*idx, *size),
            Free::Var(local) => local.clone(),
            Free::BinOp { l, r, op } => {
                let (l, r) = (self.check_free(l), self.check_free(r));
                self.check_binop(op, &l, &r);
                op.apply(&l, &r)
            }
        }
    }

    // This resolves value determined indices in `p`
    pub fn check_value(&mut self, v: &Value<Term>, p: &Fun<PosTyp>) -> Result<(), ValueErr> {
        let p_args = self.calc_args(v);
        let PosTyp = self.with_terms(p, &p_args).using_val(v, p)?;
        Ok(())
    }

    pub fn spine(&mut self, n: &Fun<NegTyp>, s: &Value<Term>) -> Result<Fun<PosTyp>, ValueErr> {
        let n_args = self.calc_args(s);
        let typ = self.with_terms(n, &n_args).using_val(s, n)?;
        Ok(typ.ret)
    }

    pub fn check_expr(mut self, l: &Lambda<Term>, n: &Fun<NegTyp>) -> Result<(), ValueErr> {
        let neg = self.extract(n);
        let e = l.inst(&neg.terms);
        self.check_expr_pos(&e, &neg.inner.ret)
    }

    pub fn check_expr_pos(
        mut self,
        expr: &Spanned<Expr<Term>>,
        p: &Fun<PosTyp>,
    ) -> Result<(), ValueErr> {
        match &expr.val {
            Expr::Return(v) => {
                self.check_value(v, p)?;
                self.check_empty().using(expr, p)?;
            }
            Expr::App(func, s, l) => {
                let n = self.infer_func(func);
                let bound_p = self.spine(&n, s)?;
                self.check_expr(l, &bound_p.arrow(p.clone()))?;
            }
            Expr::Cont(c, n, e) => {
                self.without_alloc().check_expr(c, n)?;
                self.check_expr_pos(e, p)?;
            }
            Expr::Match(free, pats) => {
                let term = self.check_free(free);
                let size = term.get_size();
                let (last_e, pats) = pats.split_last().unwrap();

                for (i, e) in pats.iter().enumerate() {
                    // we want to preserve resources between branches
                    let mut this = self.clone();
                    let phi = term.eq(&Term::nat(i as i64, size));
                    this.assume.assumptions.push(phi);
                    this.check_expr_pos(e, p)?;
                }

                let phi = Term::nat(pats.len() as i64, size).ule(&term);
                self.assume.assumptions.push(phi);
                self.check_expr_pos(last_e, p)?;
            }
            Expr::Loop(n, s) => {
                let res = self.spine(n, s)?;
                self.sub_pos_typ(&res, p).using(expr, p)?;
            }
            Expr::Debug(e) => {
                eprintln!("start #debug");
                for (name, ctx) in &self.forall {
                    // eprintln!("{name:?} {ctx:?}");
                }
                self.check_expr_pos(e, p)?;
            }
        }
        Ok(())
    }

    pub fn without_alloc(&self) -> Self {
        Self {
            assume: self.assume.clone(),
            forall: HashMap::new(),
            removed: Vec::new(),
            scope: None,
        }
    }

    pub fn check_empty(self) -> Result<(), EmptyErr> {
        for (_name, arg) in &self.forall {
            let empty = arg.clone().is_empty();
            assert!(self.assume.is_always_true(empty));
        }
        Ok(())
    }
}

trait IntoExprErr<T> {
    fn using(self, expr: &Spanned<Expr<Term>>, typ: &Fun<PosTyp>) -> Result<T, ValueErr>;
    fn using_val<X>(self, expr: &Value<Term>, typ: &Fun<X>) -> Result<T, ValueErr>;
}

impl<T, E> IntoExprErr<T> for Result<T, E>
where
    E: Diagnostic + Send + Sync + 'static,
{
    fn using(self, expr: &Spanned<Expr<Term>>, typ: &Fun<PosTyp>) -> Result<T, ValueErr> {
        self.map_err(|err| AppendLabels {
            prefix: "While checking the expression against the type, ",
            inner: Box::new(err),
            extra: vec![
                LabeledSpan::at(expr.span, "The expression"),
                LabeledSpan::at(typ.span.unwrap(), "The type"),
            ],
        })
    }

    fn using_val<X>(self, val: &Value<Term>, typ: &Fun<X>) -> Result<T, ValueErr> {
        self.map_err(|err| AppendLabels {
            prefix: "While checking the value against the type, ",
            inner: Box::new(err),
            extra: vec![
                LabeledSpan::at(val.span.unwrap(), "The value"),
                LabeledSpan::at(typ.span.unwrap(), "The type"),
            ],
        })
    }
}

#[derive(Error, Diagnostic, Debug)]
#[error("Can not leak resource")]
pub struct EmptyErr {
    #[label = "The resource"]
    span: Option<SourceSpan>,
}

type ValueErr = AppendLabels;
