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
                let mut res = env.get_kind(*idx).whnf();
                for arg in args {
                    let lazy::Kind::Pi(arg_ty, mut ret_ty) = res else {panic!()};
                    arg.check(env, arg_ty.whnf());

                    ret_ty.env[0] = Some(Lazy::new(arg.clone()));
                    res = ret_ty.whnf();
                }
                assert_eq!(res, ty)
            }
        }
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
                let mut res = env.get_fam(*idx).whnf();
                for arg in args {
                    let lazy::Fam::Pi(arg_ty, mut ret_ty) = res else {panic!()};
                    arg.check(env, arg_ty.whnf());

                    ret_ty.env[0] = Some(Lazy::new(arg.clone()));
                    res = ret_ty.whnf();
                }
                assert_eq!(res, ty)
            }
        }
    }
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

impl<T: Whnf> Lazy<T> {
    fn new(value: T) -> Self {
        Self {
            env: vec![],
            term: Box::new(value),
        }
    }

    fn whnf(&self) -> T::Target {
        self.term.whnf(&self.env)
    }
}

trait Whnf {
    type Target: PartialEq;
    fn whnf(&self, env: &[Option<Lazy<Obj>>]) -> Self::Target;
}

impl<T: Whnf> PartialEq for Lazy<T> {
    fn eq(&self, other: &Self) -> bool {
        self.whnf() == other.whnf()
    }
}

impl Whnf for Kind {
    type Target = lazy::Kind;

    fn whnf(&self, env: &[Option<Lazy<Obj>>]) -> Self::Target {
        match self.clone() {
            Kind::Ty => lazy::Kind::Ty,
            Kind::Pi(arg_ty, ret_ty) => lazy::Kind::Pi(
                Lazy {
                    env: env.to_owned(),
                    term: arg_ty,
                },
                Lazy {
                    env: add_none(env),
                    term: ret_ty,
                },
            ),
        }
    }
}

impl Whnf for Fam {
    type Target = lazy::Fam;

    fn whnf(&self, env: &[Option<Lazy<Obj>>]) -> Self::Target {
        match self.clone() {
            Fam::Pi(arg_ty, ret_ty) => lazy::Fam::Pi(
                Lazy {
                    env: env.to_owned(),
                    term: arg_ty,
                },
                Lazy {
                    env: add_none(env),
                    term: ret_ty,
                },
            ),
            Fam::Abs(body) => lazy::Fam::Abs(Lazy {
                env: add_none(env),
                term: body,
            }),
            Fam::Neutral(var, args) => {
                let args = args.iter().map(|arg| Lazy {
                    env: env.to_owned(),
                    term: Box::new(arg.clone()),
                });
                lazy::Fam::Neutral(var, args.collect())
            }
        }
    }
}

impl Whnf for Obj {
    type Target = lazy::Obj;

    fn whnf(&self, env: &[Option<Lazy<Obj>>]) -> Self::Target {
        match self.clone() {
            Obj::Abs(body) => lazy::Obj::Abs(Lazy {
                env: add_none(env),
                term: body,
            }),
            Obj::Neutral(var, args) => {
                let args = args.iter().map(|arg| Lazy {
                    env: env.to_owned(),
                    term: Box::new(arg.clone()),
                });

                let Some(res) = env.get(var).and_then(Option::as_ref) else {
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

enum Env<'a> {
    Empty {
        kinds: Vec<Lazy<Kind>>,
        families: Vec<Lazy<Fam>>,
    },
    Cons {
        ty: &'a Lazy<Fam>,
        prev: &'a Env<'a>,
    },
}

impl<'a> Env<'a> {
    fn get_kind(&self, idx: usize) -> &Lazy<Kind> {
        match self {
            Env::Empty { kinds, families } => &kinds[idx],
            Env::Cons { ty, prev } => prev.get_kind(idx),
        }
    }

    fn get_fam(&self, idx: usize) -> &Lazy<Fam> {
        match self {
            Env::Empty { kinds, families } => &families[idx],
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
