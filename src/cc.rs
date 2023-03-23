#![allow(unused)]
use std::{iter::zip, rc::Rc};

#[derive(Debug, Clone, PartialEq, Eq)]
enum Kind {
    Ty,
    Pi(Box<Fam>, Box<Kind>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum Fam {
    Pi(Box<Fam>, Box<Fam>),
    Abs(Box<Fam>),
    Neutral(usize, Vec<Obj>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum Obj {
    Abs(Box<Obj>),
    Neutral(usize, Vec<Obj>),
}

impl Kind {
    fn check(&self, env: &Env<'_>) {
        match self {
            Kind::Ty => {}
            Kind::Pi(arg_ty, ret_ty) => {
                arg_ty.check(env, &Kind::Ty);
                ret_ty.check(env);
            }
        }
    }

    fn subst(&self, idx: usize, val: &Obj) -> Box<Self> {
        let res = match self {
            Kind::Ty => Kind::Ty,
            Kind::Pi(arg_ty, ret_ty) => {
                Kind::Pi(arg_ty.subst(idx, val), ret_ty.subst(idx + 1, val))
            }
        };
        Box::new(res)
    }
}

impl Fam {
    fn check(&self, env: &Env<'_>, ty: &Kind) {
        match self {
            Fam::Pi(arg_ty, ret_ty) => {
                let Kind::Ty = ty else { panic!() };
                arg_ty.check(env, &Kind::Ty);
                ret_ty.check(env, &Kind::Ty);
            }
            Fam::Abs(body) => {
                let Kind::Pi(arg_ty, ret_ty) = ty else { panic!() };
                let env = env.push(arg_ty);
                body.check(&env, ret_ty);
            }
            Fam::Neutral(idx, args) => {
                let mut res = env.get_kind(*idx).clone();
                for arg in args {
                    let Kind::Pi(arg_ty, ret_ty) = res else { panic!() };
                    arg.check(env, &arg_ty);
                    res = *ret_ty;
                }
            }
        }
    }

    fn subst(&self, idx: usize, val: &Obj) -> Box<Self> {
        let res = match self {
            Fam::Pi(arg_ty, ret_ty) => Fam::Pi(arg_ty.subst(idx, val), ret_ty.subst(idx + 1, val)),
            Fam::Abs(body) => Fam::Abs(body.subst(idx + 1, val)),
            Fam::Neutral(i, args) => {
                Fam::Neutral(*i, args.iter().map(|x| *x.subst(idx, val)).collect())
            }
        };
        Box::new(res)
    }
}

impl Obj {
    fn check(&self, env: &Env<'_>, ty: &Fam) {
        match self {
            Obj::Abs(body) => {
                let Fam::Pi(arg_ty, ret_ty) = ty else { panic!() };
                let env = env.push(arg_ty);
                body.check(&env, ret_ty);
            }
            Obj::Neutral(idx, args) => {
                let mut res = env.get_fam(*idx).clone();
                for arg in args {
                    let Fam::Pi(arg_ty, ret_ty) = res else { panic!() };
                    arg.check(env, &arg_ty);
                    res = *ret_ty;
                }
            }
        }
    }

    fn subst(&self, idx: usize, val: &Obj) -> Box<Self> {
        let res = match self {
            Obj::Abs(body) => *body.subst(idx + 1, val),
            Obj::Neutral(i, args) => {
                if *i != idx {
                    return Obj::Neutral(*i, args);
                }
                todo!()
            }
        };
        Box::new(res)
    }
}

enum Env<'a> {
    Empty,
    Cons { ty: &'a Fam, prev: &'a Env<'a> },
}

impl<'a> Env<'a> {
    fn get_kind(&self, idx: usize) -> &Kind {
        todo!()
    }

    fn get_fam(&self, idx: usize) -> &Fam {
        match self {
            Env::Empty => panic!(),
            Env::Cons { ty, prev } => match idx.checked_sub(1) {
                Some(idx) => prev.get_fam(idx),
                None => ty,
            },
        }
    }

    fn push<'x>(&'x self, ty: &'x Fam) -> Env<'x> {
        Env::Cons { ty, prev: self }
    }
}

// mod tests {
//     use super::Term;

//     use Term::*;

//     fn pi(r: Term) -> Term {
//         Pi(Box::new(r))
//     }
//     fn abs(r: Term) -> Term {
//         Abs(Box::new(r))
//     }
//     fn var(i: usize, ty: Term) -> Term {
//         Var(i, Box::new(ty))
//     }

//     fn boolean() -> Term {
//         pi(pi(pi(var(2, Prop))))
//     }

//     fn tt() -> Term {
//         abs(abs(abs(var(1, var(2, Prop)))))
//     }

//     fn id_ty() -> Term {
//         pi(pi(var(1, Prop)))
//     }
//     fn id() -> Term {
//         abs(abs(var(0, var(1, Prop))))
//     }

//     #[test]
//     fn test() {
//         // id().check_ty(&id_ty());
//         // abs(Prop, Var(0)).check_ty(&pi(Prop, Prop));
//         // tt().check_ty(&boolean());
//         id().check_ty(&boolean());
//     }
// }
