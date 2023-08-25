use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, Inj, InnerTerm, Lambda, NegTyp, PosTyp, Prop, Sort, Term, Value, Var};

fn var(idx: &Var, proj: usize) -> Rc<Value<Var>> {
    Rc::new(Value {
        thunk: vec![],
        inj: vec![Inj::Var(idx.clone(), proj)],
    })
}

fn id_unit() -> Lambda<Var> {
    parse_lambda!(Var; _val => return ())
}

fn id_fun() -> Lambda<Var> {
    parse_lambda!(Var; val => return (val.0))
}

pub(super) fn unqualified<T>(val: impl Fn() -> T + 'static) -> Fun<T> {
    Fun {
        tau: vec![],
        fun: Rc::new(move |_| ((val)(), vec![])),
    }
}

fn forall(fun: impl Fn(Rc<Term>) -> NegTyp + 'static) -> Fun<NegTyp> {
    Fun {
        tau: vec![Sort::Nat],
        fun: Rc::new(move |args| ((fun)(args[0].clone()), vec![])),
    }
}

fn exists(fun: impl Fn(Rc<Term>) -> PosTyp + 'static) -> Fun<PosTyp> {
    Fun {
        tau: vec![Sort::Nat],
        fun: Rc::new(move |args| ((fun)(args[0].clone()), vec![])),
    }
}

fn inductive_val() -> Value<Var> {
    Value {
        thunk: vec![],
        inj: vec![Inj::Just(0, Rc::new(Value::default()))],
    }
}

fn forall_id_typ() -> Fun<NegTyp> {
    forall(|idx| NegTyp {
        arg: unqual!(&idx),
        ret: Fun {
            tau: vec![Sort::Nat],
            fun: Rc::new(move |idx2| {
                let p = unqual!(&idx2[0]);
                let prop = Prop::Eq(idx.clone(), idx2[0].clone());
                (p, vec![Rc::new(prop)])
            }),
        },
    })
}

fn impossible_id_typ() -> Fun<NegTyp> {
    Fun {
        tau: vec![Sort::Nat, Sort::Nat],
        fun: Rc::new(|args| {
            let args_1 = args[1].clone();
            let n = NegTyp {
                arg: unqual!(&args[0]),
                ret: unqualified(move || unqual!(&args_1)),
            };
            (n, vec![])
        }),
    }
}

#[test]
fn check_id_typ() {
    let ctx = SubContext::default();
    eprintln!("== test1");
    ctx.check_expr(&id_unit(), &neg_typ!(() -> ()));
    eprintln!();
    eprintln!("== test2");
    ctx.check_expr(&id_fun(), &neg_typ!((a) -> (b)));
    eprintln!();
    eprintln!("== test3");
    ctx.check_expr(&id_fun(), &neg_typ!((a) -> (b, (a) == (b))));
    eprintln!();
    // eprintln!("== test4");
    // ctx.check_expr(&id_fun(), &impossible_id_typ())
}

#[test]
fn checkk_id_app() {
    let ctx = SubContext::default();
    eprintln!("== test1");
    let res = ctx.spine(&forall_id_typ(), &inductive_val());
    eprintln!(
        "(res.fun)(UVar(100, Nat)) = {:?}",
        (res.fun)(&[InnerTerm::UVar(100, Sort::Nat).share()])
    );
    // assert_eq!((res.fun)(&[]).0, inductive_typ(&InnerTerm::Zero.share()));
    // eprintln!();
    // eprintln!("== test2");
    // let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    // ctx.verify(&xi.w);
}
