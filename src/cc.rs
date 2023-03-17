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
    Abs(Box<Fam>, Box<Fam>),
    Neutral(usize, Vec<Obj>),
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum Obj {
    Abs(Box<Fam>, Box<Obj>),
    Neutral(usize, Vec<Obj>),
}

enum Env<'a> {
    Empty,
    Cons { ty: &'a Fam, prev: &'a Env<'a> },
}

impl Obj {
    fn inf(&self, env: &Env<'_>) -> Fam {
        match self {
            Obj::Abs(arg_ty, res) => {
                let env = env.push(arg_ty);
                Fam::Pi(arg_ty.clone(), res.inf(&env).into())
            }
            Obj::Neutral(idx, args) => {
                let mut res = env.get(*idx).clone();
                for arg in args {
                    let Fam::Pi(arg_ty, res_ty) = res else {
                        panic!()
                    };
                    assert_eq!(arg.inf(env), *arg_ty);
                    res = *res_ty;
                }
                res
            }
        }
    }
}

impl Fam {
    fn inf(&self, env: &Env<'_>) -> Kind {
        match self {
            Fam::Pi(arg_ty, res_ty) => res_ty.inf(&env.push(arg_ty)),
            Fam::Abs(arg_ty, res) => {
                let env = env.push(arg_ty);
                Kind::Pi(arg_ty.clone(), res.inf(&env).into())
            }
            Fam::Neutral(idx, args) => {
                let mut res = env.get_kind(*idx).clone();
                for arg in args {
                    let Kind::Pi(arg_ty, res_ty) = res else {
                        panic!()
                    };
                    assert_eq!(arg.inf(env), *arg_ty);
                    res = *res_ty;
                }
                res
            }
        }
    }
}

impl<'a> Env<'a> {
    fn get_kind(&self, idx: usize) -> &Kind {
        todo!()
    }

    fn get(&self, idx: usize) -> &Fam {
        match self {
            Env::Empty => panic!(),
            Env::Cons { ty, prev } => match idx.checked_sub(1) {
                Some(idx) => prev.get(idx),
                None => ty,
            },
        }
    }
    fn push<'x>(&'x self, ty: &'x Fam) -> Env<'x> {
        Env::Cons { ty, prev: self }
    }

    // // this checks that a term is well formed
    // fn norm(&self, term: &Term) -> Normal {
    //     match term {
    //         Term::Prop => Normal::Prop,
    //         Term::Pi(arg_ty, ret_ty) => {
    //             let arg_ty = self.norm(arg_ty);
    //             let ret_ty = self.push(&arg_ty).norm(ret_ty);
    //             Normal::Pi(arg_ty.into(), ret_ty.into())
    //         }
    //         Term::Abs(arg_ty, ret) => {
    //             let arg_ty = self.norm(arg_ty);
    //             let ret = self.push(&arg_ty).norm(ret);
    //             Normal::Abs(arg_ty.into(), ret.into())
    //         }
    //         Term::App(func, arg) => {
    //             let func = self.norm(func);
    //             let arg = self.norm(arg);
    //             self.apply(func, arg)
    //         }
    //         Term::Var(idx) => Normal::Neutral(*idx, vec![]),
    //     }
    // }

    // fn apply(self, func: Normal, arg: Normal) -> Self {
    //     match func {
    //         Normal::Prop => unreachable!("can not call Prop"),
    //         Normal::Pi(_, _) => unreachable!("can not call Pi"),
    //         Normal::Abs(_, ret) => ret.subst(0, arg),
    //         Normal::Neutral(idx, mut args) => {
    //             args.push(arg.clone());
    //             Normal::Neutral(idx, args)
    //         }
    //     }
    // }

    // fn infer(&self, term: &Term) -> Option<Normal> {
    //     match term {
    //         Term::Prop => None,
    //         // norm arg_ty might diverge
    //         Term::Pi(arg_ty, ret_ty) => self.push(&arg_ty.norm()).infer(ret_ty),
    //         Term::Abs(arg_ty, ret) => {
    //             let ret_ty = self.push(&arg_ty.norm()).infer(ret).unwrap();
    //             Some(Normal::Pi(arg_ty.clone(), ret_ty.into()))
    //         }
    //         Term::App(func, arg) => {
    //             let Normal::Pi(arg_ty, ret_ty) = self.infer(func).unwrap() else {
    //                 panic!()
    //             };
    //             assert_eq!(self.infer(arg), Some(*arg_ty));
    //             Some(ret_ty.subst(0, &arg.norm()))
    //         }
    //         Term::Var(idx) => Some(self.get(idx).clone()),
    //     }
    // }

    // fn infer_norm(&self, term: &Normal) -> Option<Normal> {
    //     match term {
    //         Normal::Prop => None,
    //         Normal::Pi(arg_ty, ret_ty) => self.push(arg_ty).infer_norm(ret_ty),
    //         Normal::Abs(arg_ty, ret) => {
    //             let ret_ty = self.push(arg_ty).infer_norm(ret).unwrap();
    //             Some(Normal::Pi(arg_ty.clone(), ret_ty.into()))
    //         }
    //         Normal::Neutral(idx, args) => {
    //             let mut ty = self.get(*idx).clone();
    //             for arg in args {
    //                 // let arg_ty_ = self.infer_norm(arg).unwrap();
    //                 let Normal::Pi(arg_ty, ret_ty) = ty else {
    //                     panic!()
    //                 };
    //                 // assert_eq!(*arg_ty, arg_ty_);
    //                 ty = ret_ty.subst(0, arg);
    //             }
    //             Some(ty)
    //         }
    //     }
    // }
}

// impl Normal {
//     fn lift(&self, above: usize) -> Self {
//         let lift = |term: &Normal| Box::new(term.lift(above));
//         let lift1 = |term: &Normal| Box::new(term.lift(above + 1));
//         match self {
//             Normal::Prop => Normal::Prop,
//             Normal::Pi(a, r) => Normal::Pi(lift(a), lift1(r)),
//             Normal::Abs(a, r) => Normal::Abs(lift(a), lift1(r)),
//             Normal::Neutral(idx, args) => {
//                 let args = args.iter().map(|x| *lift(x)).collect();
//                 if *idx >= above {
//                     Normal::Neutral(*idx + 1, args)
//                 } else {
//                     Normal::Neutral(*idx, args)
//                 }
//             }
//         }
//     }

//     fn subst(&self, var: usize, val: &Normal) -> Self {
//         let subst = |term: &Normal| Box::new(term.subst(var, val));
//         let lift = |term: &Normal| Box::new(term.subst(var + 1, &val.lift(0)));
//         match self {
//             Normal::Prop => Normal::Prop,
//             Normal::Pi(a, r) => Normal::Pi(subst(a), lift(r)),
//             Normal::Abs(a, r) => Normal::Abs(subst(a), lift(r)),
//             Normal::Neutral(idx, args) => {
//                 if *idx == var {
//                     args.iter().fold(val.clone(), |res, arg| res.apply(arg))
//                 } else {
//                     let args = args.iter().map(|x| *subst(x)).collect();
//                     Normal::Neutral(*idx, args)
//                 }
//             }
//         }
//     }

//     fn apply(self, arg: &Normal) -> Self {
//         match self {
//             Normal::Prop => unreachable!("can not call Prop"),
//             Normal::Pi(_, _) => unreachable!("can not call Pi"),
//             Normal::Abs(_, ret) => ret.subst(0, arg),
//             Normal::Neutral(idx, mut args) => {
//                 args.push(arg.clone());
//                 Normal::Neutral(idx, args)
//             }
//         }
//     }
// }

impl Term {
    // fn check_eq(self, other: Self) {
    //     match (self.norm(), other.norm()) {
    //         (Hnf::Prop, Hnf::Prop) => {}
    //         (Hnf::Pi(ret1), Hnf::Pi(ret2)) => {
    //             ret1.check_eq(*ret2);
    //         }
    //         (Hnf::Abs(body), Hnf::Abs(body2)) => {
    //             body.check_eq(*body2);
    //         }
    //         (Hnf::Neutral(idx1, args1), Hnf::Neutral(idx2, args2)) => {
    //             assert_eq!(idx1, idx2);
    //             for (arg1, arg2) in zip(args1, args2) {
    //                 arg1.check_eq(arg2);
    //             }
    //         }
    //         (a, b) => panic!("not equal {a:?} != {b:?}"),
    //     }
    // }

    // fn check_ty(&self, ty: &Term) {
    //     let full_ty = ty.expand().push(ty.clone());
    //     let term_ty = self.expand();
    //     assert_eq!(full_ty.len(), term_ty.len());
    //     full_ty.head().check_eq(*term_ty.head());
    // }

    // fn expand(&self) -> TyChain {
    //     match self {
    //         Term::Prop => TyChain::new(),
    //         Term::Pi(ret_ty) => ret_ty.expand(),
    //         Term::Abs(ret) => {
    //             let ret_tys = ret.expand();
    //             let pi = Term::Pi(ret_tys.head());
    //             pi.expand().push(pi)
    //         }
    //         Term::App(func, arg) => {
    //             let Term::Pi(ret_ty) = *func.expand().head() else {
    //                 panic!("can only call functions")
    //             };
    //             let x = ret_ty.subst(0, arg);
    //             x.expand().push(*x)
    //         }
    //         Term::Var(var, ty) => ty.expand().push(ty.as_ref().clone()),
    //     }
    // }
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
    fn len(&self) -> usize {
        match self {
            TyChain::Cons { val: _, rst } => rst.len() + 1,
            TyChain::Empty => 0,
        }
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
