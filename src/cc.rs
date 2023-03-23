#![allow(unused)]
use std::{iter::zip, rc::Rc};

#[derive(Debug, Clone, PartialEq)]
enum Kind {
    Ty,
    Pi(Box<Fam>, Box<Kind>),
}
#[derive(Debug, Clone, PartialEq)]
enum Fam {
    Pi(Box<Fam>, Box<Fam>),
    Abs(Box<Fam>),
    Neutral(usize, Vec<Obj>),
}
#[derive(Debug, Clone, PartialEq)]
enum Obj {
    Abs(Box<Obj>),
    Neutral(usize, Vec<Obj>),
}

fn add_none(env: &[Option<Lazy<Obj>>]) -> Vec<Option<Lazy<Obj>>> {
    let mut new = vec![None];
    new.extend_from_slice(env);
    new
}

mod lazy {
    #[derive(Debug, Clone)]
    pub(super) struct Lazy<T> {
        pub env: Vec<Option<Lazy<super::Obj>>>,
        pub term: Box<T>,
    }

    #[derive(Debug, Clone, PartialEq)]
    pub(super) enum Kind {
        Ty,
        Pi(Lazy<super::Fam>, Lazy<super::Kind>),
    }
    #[derive(Debug, Clone, PartialEq)]
    pub(super) enum Fam {
        Pi(Lazy<super::Fam>, Lazy<super::Fam>),
        Abs(Lazy<super::Fam>),
        Neutral(usize, Vec<Lazy<super::Obj>>),
    }
    #[derive(Debug, Clone, PartialEq)]
    pub(super) enum Obj {
        Abs(Lazy<super::Obj>),
        Neutral(usize, Vec<Lazy<super::Obj>>),
    }
}

use lazy::Lazy;

impl<T> Lazy<T> {
    fn new(value: T) -> Self {
        Self {
            env: vec![],
            term: Box::new(value),
        }
    }
}

impl Kind {
    fn check(&self, env: &Env<'_>) {
        match self {
            Kind::Ty => {}
            Kind::Pi(arg_ty, ret_ty) => {
                arg_ty.check(env, lazy::Kind::Ty);
                ret_ty.check(env);
            }
        }
    }
}

impl Lazy<Kind> {
    fn whnf(&self) -> lazy::Kind {
        match *self.term.clone() {
            Kind::Ty => lazy::Kind::Ty,
            Kind::Pi(arg_ty, ret_ty) => lazy::Kind::Pi(
                Lazy {
                    env: self.env.clone(),
                    term: arg_ty,
                },
                Self {
                    env: add_none(&self.env),
                    term: ret_ty,
                },
            ),
        }
    }
}

impl PartialEq for Lazy<Kind> {
    fn eq(&self, other: &Self) -> bool {
        self.whnf() == other.whnf()
    }
}

impl Fam {
    fn check(&self, env: &Env<'_>, ty: lazy::Kind) {
        match self {
            Fam::Pi(arg_ty, ret_ty) => {
                let lazy::Kind::Ty = ty else {panic!()};
                arg_ty.check(env, lazy::Kind::Ty);
                ret_ty.check(env, lazy::Kind::Ty);
            }
            Fam::Abs(body) => {
                let lazy::Kind::Pi(arg_ty, ret_ty) = ty else {panic!()};
                let env = env.push(&arg_ty);
                body.check(&env, ret_ty.whnf());
            }
            Fam::Neutral(idx, args) => {
                let mut res = env.get_kind(*idx).clone();
                for arg in args {
                    let lazy::Kind::Pi(arg_ty, ret_ty) = res.whnf() else {panic!()};
                    arg.check(env, arg_ty.whnf());

                    res = ret_ty.clone();
                    res.env[0] = Some(Lazy::new(arg.clone()))
                }
                assert_eq!(res.whnf(), ty)
            }
        }
    }
}

impl Lazy<Fam> {
    fn whnf(&self) -> lazy::Fam {
        match *self.term.clone() {
            Fam::Pi(arg_ty, ret_ty) => lazy::Fam::Pi(
                Lazy {
                    env: self.env.clone(),
                    term: arg_ty,
                },
                Self {
                    env: add_none(&self.env),
                    term: ret_ty,
                },
            ),
            Fam::Abs(body) => lazy::Fam::Abs(Lazy {
                env: add_none(&self.env),
                term: body,
            }),
            Fam::Neutral(var, args) => {
                let args = args.iter().map(|arg| Lazy {
                    env: self.env.clone(),
                    term: Box::new(arg.clone()),
                });
                lazy::Fam::Neutral(var, args.collect())
            }
        }
    }
}

impl PartialEq for Lazy<Fam> {
    fn eq(&self, other: &Self) -> bool {
        self.whnf() == other.whnf()
    }
}

impl Obj {
    fn check(&self, env: &Env<'_>, ty: lazy::Fam) {
        match self {
            Obj::Abs(body) => {
                let lazy::Fam::Pi(arg_ty, ret_ty) = ty else {panic!()};
                let env = env.push(&arg_ty);
                body.check(&env, ret_ty.whnf());
            }
            Obj::Neutral(idx, args) => {
                let mut res = env.get_fam(*idx).clone();
                for arg in args {
                    let lazy::Fam::Pi(arg_ty, ret_ty) = res.whnf() else {panic!()};
                    arg.check(env, arg_ty.whnf());

                    res = ret_ty;
                    res.env[0] = Some(Lazy::new(arg.clone()))
                }
                assert_eq!(res.whnf(), ty)
            }
        }
    }
}

impl lazy::Obj {
    fn add_arg(self, arg: Lazy<Obj>) -> Self {
        match self {
            lazy::Obj::Abs(mut body) => {
                assert_eq!(body.env[0], None);
                body.env[0] = Some(arg);
                body.whnf()
            }
            lazy::Obj::Neutral(var, mut args) => {
                args.push(arg);
                lazy::Obj::Neutral(var, args)
            }
        }
    }
}

impl Lazy<Obj> {
    fn whnf(&self) -> lazy::Obj {
        match *self.term.clone() {
            Obj::Abs(body) => lazy::Obj::Abs(Lazy {
                env: add_none(&self.env),
                term: body,
            }),
            Obj::Neutral(var, args) => {
                let args = args.iter().map(|arg| Lazy {
                    env: self.env.clone(),
                    term: Box::new(arg.clone()),
                });

                let Some(mut res) = self.env.get(var).and_then(Option::as_ref) else {
                    return lazy::Obj::Neutral(var, args.collect())
                };

                let mut res = res.whnf();
                for arg in args {
                    res = res.add_arg(arg);
                }
                res
            }
        }
    }
}

impl PartialEq for Lazy<Obj> {
    fn eq(&self, other: &Self) -> bool {
        self.whnf() == other.whnf()
    }
}

enum Env<'a> {
    Empty,
    Cons {
        ty: &'a Lazy<Fam>,
        prev: &'a Env<'a>,
    },
}

impl<'a> Env<'a> {
    fn get_kind(&self, idx: usize) -> &Lazy<Kind> {
        todo!()
    }

    fn get_fam(&self, idx: usize) -> &Lazy<Fam> {
        match self {
            Env::Empty => panic!(),
            Env::Cons { ty, prev } => match idx.checked_sub(1) {
                Some(idx) => prev.get_fam(idx),
                None => ty,
            },
        }
    }

    fn push<'x>(&'x self, ty: &'x Lazy<Fam>) -> Env<'x> {
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
