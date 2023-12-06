use std::{
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

use z3::{ast::Bool, FuncDecl, Sort};

use crate::solver::ctx;

use super::{term::Term, typing::zip_eq};

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub enum FuncTerm {
    Free(Rc<FuncDecl<'static>>),
    User(Rc<dyn Fn(&[Term]) -> Term>),
}

impl FuncTerm {
    pub fn new<F: Fn(&[Term]) -> Term + 'static>(f: F) -> Self {
        Self::User(Rc::new(f))
    }

    pub fn new_bool<F: Fn(&[Term]) -> Bool<'static> + 'static>(f: F) -> Self {
        Self::new(move |x| Term::Bool((f)(x)))
    }

    pub fn apply_bool(&self, idx: &[Term]) -> Bool<'static> {
        self.apply(idx).to_bool()
    }

    pub fn apply(&self, idx: &[Term]) -> Term {
        match self {
            FuncTerm::Free(f) => {
                let args: Vec<_> = idx.iter().map(|x| x.to_bv()).collect();
                let args: Vec<_> = args.iter().map(|x| x as _).collect();
                let val = f.apply(&args);
                if let Some(b) = val.as_bool() {
                    Term::Bool(b)
                } else if let Some(bv) = val.as_bv() {
                    Term::BV(bv)
                } else {
                    panic!()
                }
            }
            FuncTerm::User(func) => (func)(idx),
        }
    }

    pub fn difference(&self, other: &Self) -> Self {
        let this = self.clone();
        let other = other.clone();
        Self::new_bool(move |idx| this.apply_bool(idx) & !other.apply_bool(idx))
    }

    pub fn ite(&self, then: &Self, other: &Self) -> Self {
        let (cond, then, other) = (self.clone(), then.clone(), other.clone());
        Self::new(move |idx| {
            let (then, other) = (then.apply(idx).to_bv(), other.apply(idx).to_bv());
            assert_eq!(then.get_size(), other.get_size());
            Term::BV(cond.apply_bool(idx).ite(&then, &other))
        })
    }

    pub fn exactly(ptr: &[Term]) -> Self {
        let ptr = ptr.to_owned();
        Self::new_bool(move |val| {
            zip_eq(&ptr, val)
                .map(|(l, r)| l.eq(r).to_bool())
                .fold(Bool::from_bool(ctx(), true), |l, r| l & r)
        })
    }

    pub fn always(val: Term) -> Self {
        Self::new(move |_x| val.clone())
    }

    pub fn and(&self, other: &Self) -> Self {
        let this = self.clone();
        let other = other.clone();
        Self::new_bool(move |idx| this.apply_bool(idx) & other.apply_bool(idx))
    }

    pub fn free(arg_size: &[(u32, String)]) -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        let name = format!("heap-{}", ID.fetch_add(1, Ordering::Relaxed));
        let domain: Vec<_> = arg_size
            .iter()
            .map(|(sz, _name)| Sort::bitvector(ctx(), *sz))
            .collect();
        let domain: Vec<_> = domain.iter().collect();
        let f = FuncDecl::new(ctx(), name, &domain, &Sort::bitvector(ctx(), 8));
        Self::Free(Rc::new(f))
    }
}
