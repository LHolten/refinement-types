use std::rc::Rc;

use super::{Expr, FullContext, Fun, Inj, InnerTerm, Measured, NegTyp, PosTyp, Sort, Term, Value};

fn var(idx: usize, proj: usize) -> Rc<Value> {
    Rc::new(Value {
        thunk: vec![],
        inj: vec![Inj::Var(idx, proj)],
    })
}

fn id_fun() -> Expr {
    Expr::Return(var(0, 0))
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

fn forall(fun: impl Fn(&Rc<Term>) -> NegTyp + 'static) -> Fun<NegTyp> {
    Fun {
        tau: vec![Sort::Nat],
        fun: Rc::new(move |args| ((fun)(&args[0]), vec![])),
    }
}

fn exists(fun: impl Fn(&Rc<Term>) -> PosTyp + 'static) -> Fun<PosTyp> {
    Fun {
        tau: vec![Sort::Nat],
        fun: Rc::new(move |args| ((fun)(&args[0]), vec![])),
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
    exists(inductive_typ)
}

fn forall_id_typ() -> Fun<NegTyp> {
    forall(|idx| {
        let idx = idx.clone();
        NegTyp {
            arg: inductive_typ(&idx),
            ret: unqualified(move || inductive_typ(&idx)),
        }
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
    let ctx = FullContext::default();
    eprintln!("== test1");
    ctx.check_expr(&id_fun(), &id_typ(unit_typ()));
    eprintln!();
    eprintln!("== test2");
    ctx.check_expr(&id_fun(), &id_typ(existential_typ()));
    eprintln!();
    eprintln!("== test3");
    ctx.check_expr(&id_fun(), &forall_id_typ());
    eprintln!();
    eprintln!("== test4");
    ctx.check_expr(&id_fun(), &impossible_id_typ())
}

#[test]
fn checkk_id_app() {
    let ctx = FullContext::default();
    eprintln!("== test1");
    let res = ctx.spine(&forall_id_typ(), &inductive_val());
    assert_eq!(res, unqualified(|| inductive_typ(&InnerTerm::Zero.share())));
    // eprintln!();
    // eprintln!("== test2");
    // let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    // ctx.verify(&xi.w);
}
