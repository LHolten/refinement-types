#![allow(unused, non_snake_case)]

use std::rc::Rc;

trait Checkable {
    type Ty;
    type Out;

    fn check(&self, ty: &Self::Ty) -> Rc<Self::Out>;
}

trait Map<T>
where
    T: Checkable,
{
    fn map(&self, obj: &Rc<Obj>) -> Rc<T>;
    fn cmap(&self, obj: &Rc<CObj>) -> Rc<T::Out>;
}

enum Kind {
    Type,
    Pi(Rc<Fam>, Rc<dyn Map<Kind>>),
}

enum CKind {
    Type,
    Pi(Rc<CFam>, Rc<dyn Map<Kind>>),
}

enum Fam {
    Pi(Rc<Fam>, Rc<dyn Map<Fam>>),
    Abs(Rc<dyn Map<Fam>>),
    Neutral(Rc<()>, Rc<CKind>, Vec<Rc<Obj>>),
}

enum CFam {
    Pi(Rc<CFam>, Rc<dyn Map<Fam>>),
    Abs(Rc<dyn Map<Fam>>),
    Neutral(Rc<()>, Vec<Rc<CObj>>),
}

enum Obj {
    Abs(Rc<dyn Map<Obj>>),
    Neutral(Rc<()>, Rc<CFam>, Vec<Rc<Obj>>),
}

enum CObj {
    Abs(Rc<dyn Map<Obj>>),
    Neutral(Rc<()>, Vec<Rc<CObj>>),
}

impl Kind {
    pub fn pi(ty: &Rc<Fam>, f: impl Map<Kind> + 'static) -> Rc<Self> {
        Rc::new(Kind::Pi(ty.clone(), Rc::new(f)))
    }
}

impl Fam {
    pub fn var(ty: &Rc<CKind>) -> Rc<Self> {
        Rc::new(Fam::Neutral(Rc::new(()), ty.clone(), vec![]))
    }
    pub fn pi(ty: &Rc<Fam>, f: impl Map<Fam> + 'static) -> Rc<Self> {
        Rc::new(Fam::Pi(ty.clone(), Rc::new(f)))
    }
    pub fn abs(f: impl Map<Fam> + 'static) -> Rc<Self> {
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
    pub fn var(ty: &Rc<CFam>) -> (Rc<CObj>, Rc<Self>) {
        let x = Rc::new(());
        (
            Rc::new(CObj::Neutral(x.clone(), vec![])),
            Rc::new(Obj::Neutral(x, ty.clone(), vec![])),
        )
    }
    pub fn abs(f: impl Map<Obj> + 'static) -> Rc<Self> {
        Rc::new(Obj::Abs(Rc::new(f)))
    }
}

impl CObj {
    pub fn var() -> Rc<Self> {
        Rc::new(CObj::Neutral(Rc::new(()), vec![]))
    }
    pub fn expand(&self) -> Rc<Obj> {
        todo!()
    }
    // pub fn abs(f: impl Fn(&Rc<CObj>) -> Rc<CObj> + 'static) -> Rc<Self> {
    //     Rc::new(CObj::Abs(Rc::new(f)))
    // }
}

impl Checkable for Kind {
    type Ty = ();
    type Out = CKind;

    fn check(&self, (): &Self::Ty) -> Rc<Self::Out> {
        match self {
            Kind::Type => Rc::new(CKind::Type),
            Kind::Pi(a, f) => {
                let a = a.check(&CKind::Type);
                let (cvar, var) = Obj::var(&a);
                let _ = f.map(&var).check(&());
                Rc::new(CKind::Pi(a, f.clone()))
            }
        }
    }
}

impl PartialEq for CKind {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Type, Self::Type) => true,
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => {
                let true = l0 == r0 else { return false };
                let var = CObj::var();
                l1.cmap(&var) == r1.cmap(&var)
            }
            _ => false,
        }
    }
}

impl Checkable for Fam {
    type Ty = CKind;
    type Out = CFam;

    fn check(&self, ty: &Self::Ty) -> Rc<Self::Out> {
        match self {
            Fam::Pi(a, f) => {
                let a = a.check(&CKind::Type);
                let (cvar, var) = Obj::var(&a);
                let _ = f.map(&var).check(&CKind::Type);
                Rc::new(CFam::Pi(a, f.clone()))
            }
            Fam::Abs(f) => {
                let CKind::Pi(a, t) = ty else {panic!()};
                let (cvar, var) = Obj::var(a);
                let _ = f.map(&var).check(&t.cmap(&cvar));
                Rc::new(CFam::Abs(f.clone()))
            }
            Fam::Neutral(x, r, args) => {
                let mut new_args = vec![];
                let mut res = r.clone();
                for arg in args {
                    let CKind::Pi(a, t) = res.as_ref() else {panic!()};
                    let arg = arg.check(a);
                    res = t.cmap(&arg);
                    new_args.push(arg);
                }
                assert!(res.as_ref() == ty);
                Rc::new(CFam::Neutral(x.clone(), new_args))
            }
        }
    }
}

impl PartialEq for CFam {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Pi(l0, l1), Self::Pi(r0, r1)) => {
                let true = l0 == r0 else { return false };
                let var = CObj::var();
                l1.cmap(&var) == r1.cmap(&var)
            }
            (Self::Abs(l0), Self::Abs(r0)) => {
                let var = CObj::var();
                l0.cmap(&var) == r0.cmap(&var)
            }
            (Self::Neutral(l0, l1), Self::Neutral(r0, r1)) => {
                let true = Rc::ptr_eq(l0, r0) else { return false };
                l1 == r1
            }
            _ => false,
        }
    }
}

impl Checkable for Obj {
    type Ty = CFam;
    type Out = CObj;

    fn check(&self, ty: &Self::Ty) -> Rc<Self::Out> {
        match self {
            Obj::Abs(f) => {
                let CFam::Pi(a, t) = ty else {panic!()};
                let (cvar, var) = Obj::var(a);
                let _ = f.map(&var).check(&t.cmap(&cvar));
                Rc::new(CObj::Abs(f.clone()))
            }
            Obj::Neutral(x, r, args) => {
                let mut new_args = vec![];
                let mut res = r.clone();
                for arg in args {
                    let CFam::Pi(a, t) = res.as_ref() else {panic!()};
                    let arg = arg.check(a);
                    res = t.cmap(&arg);
                    new_args.push(arg);
                }
                assert!(res.as_ref() == ty);
                Rc::new(CObj::Neutral(x.clone(), new_args))
            }
        }
    }
}

impl PartialEq for CObj {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Abs(l0), Self::Abs(r0)) => {
                let var = CObj::var();
                l0.cmap(&var) == r0.cmap(&var)
            }
            (Self::Neutral(l0, l1), Self::Neutral(r0, r1)) => {
                let true = Rc::ptr_eq(l0, r0) else { return false };
                l1 == r1
            }
            _ => false,
        }
    }
}

// mod tests {
//     use std::rc::Rc;

//     use super::{CKind, Checkable, Fam, Kind, Obj};

//     #[test]
//     fn identity_test() {
//         let U = Fam::var(&Rc::new(CKind::Type));
//         let e = Fam::var(&CKind::pi(&U, |_| Rc::new(Kind::Type)));
//         let id = Obj::abs(|A| Obj::abs(|x| x.clone()));
//         let ty = Fam::pi(&U, move |A| {
//             let A = A.clone();
//             let e = e.clone();
//             Fam::pi(&Fam::app(&e, &A), move |x| Fam::app(&e, &A))
//         });
//         id.check(&ty)
//     }
// }
