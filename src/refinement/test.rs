use std::rc::Rc;

use crate::refinement::SubContext;

use super::{
    Expr, Fun, Inj, InnerTerm, Lambda, Measured, NegTyp, PosTyp, Prop, Sort, Term, Value, Var,
};

fn var(idx: &Var, proj: usize) -> Rc<Value> {
    Rc::new(Value {
        thunk: vec![],
        inj: vec![Inj::Var(idx.clone(), proj)],
    })
}

fn id_unit() -> Lambda {
    Lambda {
        lamb: Rc::new(|_idx| Expr::Return(Rc::new(Value::default()))),
    }
}

fn id_fun() -> Lambda {
    Lambda {
        lamb: Rc::new(|idx| Expr::Return(var(idx, 0))),
    }
}

fn unit_typ() -> Fun<PosTyp> {
    unqualified(PosTyp::default)
}

fn unqualified<T>(val: impl Fn() -> T + 'static) -> Fun<T> {
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

fn id_typ(arg: Fun<PosTyp>) -> Fun<NegTyp> {
    Fun {
        tau: arg.tau.clone(),
        fun: Rc::new(move |args| {
            let (tmp, props) = (arg.fun)(args);
            let n = NegTyp {
                arg: tmp,
                ret: arg.clone(),
            };
            (n, props)
        }),
    }
}

fn inductive_val() -> Value {
    Value {
        thunk: vec![],
        inj: vec![Inj::Just(0, Rc::new(Value::default()))],
    }
}

fn inductive_typ(idx: &Rc<Term>) -> PosTyp {
    PosTyp {
        measured: vec![Measured {
            f_alpha: vec![unqualified(|| (PosTyp::default(), InnerTerm::Zero.share()))],
            term: idx.clone(),
        }],
        thunks: vec![],
    }
}

fn existential_typ() -> Fun<PosTyp> {
    exists(|idx| inductive_typ(&idx))
}

fn forall_id_typ() -> Fun<NegTyp> {
    forall(|idx| NegTyp {
        arg: inductive_typ(&idx),
        ret: Fun {
            tau: vec![Sort::Nat],
            fun: Rc::new(move |idx2| {
                let p = inductive_typ(&idx2[0]);
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
                arg: inductive_typ(&args[0]),
                ret: unqualified(move || inductive_typ(&args_1)),
            };
            (n, vec![])
        }),
    }
}

#[test]
fn check_id_typ() {
    let ctx = SubContext::default();
    eprintln!("== test1");
    ctx.check_expr(&id_unit(), &id_typ(unit_typ()));
    eprintln!();
    eprintln!("== test2");
    ctx.check_expr(&id_fun(), &id_typ(existential_typ()));
    eprintln!();
    eprintln!("== test3");
    ctx.check_expr(&id_fun(), &forall_id_typ());
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
