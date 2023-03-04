use std::iter::zip;

#[derive(Debug, Clone, PartialEq, Eq)]
enum Term {
    Prop,
    Pi(Box<Term>, Box<Term>),
    Abs(Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    Var(usize),
}

enum Hnf {
    Prop,
    Pi(Box<Term>, Box<Term>),
    Abs(Box<Term>),
    Neutral(usize, Vec<Term>),
}

impl Term {
    fn subst(&self, var: usize, val: &Self) -> Self {
        match self {
            Term::Prop => Term::Prop,
            Term::Pi(_, _) => todo!(),
            Term::Abs(_, _) => todo!(),
            Term::App(_, _) => todo!(),
            Term::Var(_) => todo!(),
        }
    }

    fn norm(self, mut args: Vec<Term>) -> Hnf {
        match self {
            Term::Prop => Hnf::Prop,
            Term::Pi(arg_ty, ret_ty) => Hnf::Pi(arg_ty, ret_ty),
            Term::Abs(arg_ty, ret) => {
                if let Some(arg) = args.pop() {
                    return ret.subst(0, &arg).norm(args);
                }
                Hnf::Abs(ret)
            }
            Term::App(func, arg) => {
                args.push(*arg);
                func.norm(args)
            }
            Term::Var(idx) => Hnf::Neutral(idx, args),
        }
    }

    fn check_eq(self, other: Self) {
        match (self.norm(vec![]), other.norm(vec![])) {
            (Hnf::Prop, Hnf::Prop) => {}
            (Hnf::Pi(arg1, ret1), Hnf::Pi(arg2, ret2)) => {
                arg1.check_eq(*arg2);
                ret1.check_eq(*ret2);
            }
            (Hnf::Abs(body), Hnf::Abs(body2)) => {
                body.check_eq(*body2);
            }
            (Hnf::Neutral(idx1, args1), Hnf::Neutral(idx2, args2)) => {
                assert_eq!(idx1, idx2);
                for (arg1, arg2) in zip(args1, args2) {
                    arg1.check_eq(arg2);
                }
            }
            _ => panic!("not equal"),
        }
    }
}

struct Env;

impl Env {
    fn new() -> Self {
        todo!()
    }
    fn add(&self, ty: &Term) -> Self {
        todo!()
    }
    fn get(&self, var: usize) -> TyChain {
        todo!()
    }

    fn check_ty(&self, term: &Term, ty: &Term) {
        let full_ty = self.expand(ty).push(ty.clone());
        let term_ty = self.expand(term);

        full_ty.head().check_eq(*term_ty.head());
    }

    fn expand(&self, term: &Term) -> TyChain {
        match term {
            Term::Prop => TyChain::new(),
            Term::Pi(arg_ty, ret_ty) => self.add(arg_ty).expand(ret_ty),
            Term::Abs(arg_ty, ret) => {
                let ret_tys = self.add(arg_ty).expand(ret);
                let pi = Term::Pi(arg_ty.clone(), ret_tys.head());
                self.expand(&pi).push(pi)
            }
            Term::App(func, arg) => {
                let Term::Pi(arg_ty, ret_ty) = *self.expand(func).head() else {
                    panic!("can only call functions")
                };
                self.check_ty(arg, &arg_ty);
                let x = ret_ty.subst(0, arg);
                self.expand(&x).push(x)
            }
            Term::Var(var) => self.get(*var),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum TyChain {
    Cons { val: Term, rst: Box<Self> },
    Empty,
}

impl TyChain {
    fn new() -> Self {
        Self::Empty
    }
    fn head(&self) -> Box<Term> {
        match self {
            TyChain::Cons { val, rst: _ } => Box::new(val.clone()),
            TyChain::Empty => panic!("no more type"),
        }
    }
    fn push(self, term: Term) -> Self {
        Self::Cons {
            val: term,
            rst: Box::new(self),
        }
    }
}

mod tests {
    use super::{Env, Term};

    use Term::*;

    fn pi(a: Term, r: Term) -> Term {
        Pi(Box::new(a), Box::new(r))
    }
    fn abs(a: Term, r: Term) -> Term {
        Abs(Box::new(a), Box::new(r))
    }

    fn boolean() -> Term {
        pi(Prop, pi(Var(0), pi(Var(1), Var(2))))
    }

    fn tt() -> Term {
        abs(Prop, abs(Var(0), abs(Var(1), Var(1))))
    }

    #[test]
    fn test() {
        Env::new().check_ty(&tt(), &boolean())
    }
}
