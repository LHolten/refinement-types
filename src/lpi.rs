#![allow(unused, non_snake_case)]

use std::rc::Rc;

trait Checkable {
    type Ty;

    fn check(&self, ty: &Self::Ty);
    fn typed_eq(&self, other: &Self, ty: &Self::Ty);
}

enum Kind {
    Type,
    Pi(Rc<Fam>, Rc<dyn Fn(&Rc<Obj>) -> Rc<Kind>>),
}

enum Fam {
    Pi(Rc<Fam>, Rc<dyn Fn(&Rc<Obj>) -> Rc<Fam>>),
    Abs(Rc<dyn Fn(&Rc<Obj>) -> Rc<Fam>>),
    Neutral(Rc<()>, Rc<Kind>, Vec<Rc<Obj>>),
}

enum Obj {
    Abs(Rc<dyn Fn(&Rc<Obj>) -> Rc<Obj>>),
    Neutral(Rc<()>, Rc<Fam>, Vec<Rc<Obj>>),
}

impl Kind {
    pub fn pi(ty: &Rc<Fam>, f: impl Fn(&Rc<Obj>) -> Rc<Kind> + 'static) -> Rc<Self> {
        Rc::new(Kind::Pi(ty.clone(), Rc::new(f)))
    }
}

impl Fam {
    pub fn var(ty: &Rc<Kind>) -> Rc<Self> {
        Rc::new(Fam::Neutral(Rc::new(()), ty.clone(), vec![]))
    }
    pub fn pi(ty: &Rc<Fam>, f: impl Fn(&Rc<Obj>) -> Rc<Fam> + 'static) -> Rc<Self> {
        Rc::new(Fam::Pi(ty.clone(), Rc::new(f)))
    }
    pub fn abs(f: impl Fn(&Rc<Obj>) -> Rc<Fam> + 'static) -> Rc<Self> {
        Rc::new(Fam::Abs(Rc::new(f)))
    }
    pub fn app(val: &Rc<Self>, arg: &Rc<Obj>) -> Rc<Self> {
        let Fam::Neutral(x, a, args) = val.as_ref() else {panic!()};
        let mut args = args.clone();
        args.push(arg.clone());
        Rc::new(Fam::Neutral(x.clone(), a.clone(), args))
    }
}

impl Obj {
    pub fn var(ty: &Rc<Fam>) -> Rc<Self> {
        Rc::new(Obj::Neutral(Rc::new(()), ty.clone(), vec![]))
    }
    pub fn abs(f: impl Fn(&Rc<Obj>) -> Rc<Obj> + 'static) -> Rc<Self> {
        Rc::new(Obj::Abs(Rc::new(f)))
    }
}

impl Checkable for Kind {
    type Ty = ();

    fn check(&self, (): &Self::Ty) {
        match self {
            Kind::Type => {}
            Kind::Pi(a, f) => {
                let var = Obj::var(a);
                f(&var).check(&());
            }
        }
    }

    fn typed_eq(&self, other: &Self, (): &Self::Ty) {
        match (self, other) {
            (Self::Type, Self::Type) => {}
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => {
                l0.typed_eq(r0, &Kind::Type);
                let var = Obj::var(l0);
                l1(&var).typed_eq(&r1(&var), &())
            }
            _ => panic!(),
        }
    }
}

impl Checkable for Fam {
    type Ty = Kind;

    fn check(&self, ty: &Self::Ty) {
        match self {
            Fam::Pi(a, f) => {
                a.check(&Kind::Type);
                let var = Obj::var(a);
                f(&var).check(ty);
            }
            Fam::Abs(f) => {
                let Kind::Pi(a, t) = ty else {panic!()};
                let var = Obj::var(a);
                f(&var).check(&t(&var));
            }
            Fam::Neutral(_, r, args) => {
                let mut res = r.clone();
                for arg in args {
                    let Kind::Pi(a, t) = res.as_ref() else {panic!()};
                    arg.check(a);
                    res = t(arg);
                }
                res.typed_eq(ty, &())
            }
        }
    }

    fn typed_eq(&self, other: &Self, ty: &Self::Ty) {
        match (self, other) {
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => {
                l0.typed_eq(r0, &Kind::Type);
                let var = Obj::var(l0);
                l1(&var).typed_eq(&r1(&var), ty)
            }
            (Self::Abs(l0), Self::Abs(r0)) => {
                let Kind::Pi(a, t) = ty else {panic!()};
                let var = Obj::var(a);
                l0(&var).typed_eq(&r0(&var), &t(&var))
            }
            (Self::Neutral(l0, l1, l2), Self::Neutral(r0, r1, r2)) => {
                assert!(Rc::ptr_eq(l0, r0));
                assert_eq!(l2.len(), r2.len());

                let mut res = l1.clone();
                for (l, r) in l2.iter().zip(r2.iter()) {
                    let Kind::Pi(a, t) = res.as_ref() else {panic!()};
                    l.typed_eq(r, a);
                    res = t(l);
                }
            }
            _ => panic!(),
        }
    }
}

impl Checkable for Obj {
    type Ty = Fam;

    fn check(&self, ty: &Fam) {
        match self {
            Obj::Abs(f) => {
                let Fam::Pi(a, t) = ty else {panic!()};
                let var = Obj::var(a);
                f(&var).check(&t(&var))
            }
            Obj::Neutral(_, r, args) => {
                let mut res = r.clone();
                for arg in args {
                    let Fam::Pi(a, t) = res.as_ref() else {panic!()};
                    arg.check(a);
                    res = t(arg);
                }
                res.typed_eq(ty, &Kind::Type)
            }
        }
    }

    fn typed_eq(&self, other: &Self, ty: &Self::Ty) {
        match (self, other) {
            (Self::Abs(l0), Self::Abs(r0)) => {
                let Fam::Pi(a, t) = ty else {panic!()};
                let var = Obj::var(a);
                l0(&var).typed_eq(&r0(&var), &t(&var))
            }
            (Self::Neutral(l0, l1, l2), Self::Neutral(r0, r1, r2)) => {
                assert!(Rc::ptr_eq(l0, r0));
                assert_eq!(l2.len(), r2.len());

                let mut res = l1.clone();
                for (l, r) in l2.iter().zip(r2.iter()) {
                    let Fam::Pi(a, t) = res.as_ref() else {panic!()};
                    l.typed_eq(r, a);
                    res = t(l);
                }
            }
            _ => panic!(),
        }
    }
}

mod tests {
    use std::rc::Rc;

    use super::{Checkable, Fam, Kind, Obj};

    #[test]
    fn identity_test() {
        let U = Fam::var(&Rc::new(Kind::Type));
        let e = Fam::var(&Kind::pi(&U, |_| Rc::new(Kind::Type)));
        let id = Obj::abs(|A| Obj::abs(|x| x.clone()));
        let ty = Fam::pi(&U, move |A| {
            let A = A.clone();
            let e = e.clone();
            Fam::pi(&Fam::app(&e, &A), move |x| Fam::app(&e, &A))
        });
        id.check(&ty)
    }
}
