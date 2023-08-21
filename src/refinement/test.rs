use std::rc::Rc;

use super::{Expr, FullContext, Fun, InnerTerm, NegTyp, PosTyp, ProdFunctor, Sort, Term, Value};

fn id_fun() -> Expr {
    Expr::Lambda(Rc::new(Expr::Return(Rc::new(Value::Var(0, vec![])))))
}

fn unit_typ() -> Rc<PosTyp> {
    Rc::new(PosTyp::Prod(vec![]))
}

fn forall(fun: impl Fn(&Rc<Term>) -> Rc<NegTyp> + 'static) -> Rc<NegTyp> {
    Rc::new(NegTyp::Forall(Fun {
        tau: Sort::Nat,
        fun: Rc::new(fun),
    }))
}

fn exists(fun: impl Fn(&Rc<Term>) -> Rc<PosTyp> + 'static) -> Rc<PosTyp> {
    Rc::new(PosTyp::Exists(Fun {
        tau: Sort::Nat,
        fun: Rc::new(fun),
    }))
}

fn id_typ(arg: &Rc<PosTyp>) -> Rc<NegTyp> {
    Rc::new(NegTyp::Fun(
        arg.clone(),
        Rc::new(NegTyp::Force(arg.clone())),
    ))
}

fn inductive_val() -> Value {
    Value::Inj(0, Rc::new(Value::Tuple(vec![])))
}

fn inductive_typ(idx: &Rc<Term>) -> Rc<PosTyp> {
    Rc::new(PosTyp::Measured(
        vec![(
            Rc::new(ProdFunctor { prod: vec![] }),
            InnerTerm::Zero.share(),
        )],
        idx.clone(),
    ))
}

fn existential_typ() -> Rc<PosTyp> {
    exists(inductive_typ)
}

fn forall_id_typ() -> Rc<NegTyp> {
    forall(|idx| {
        let m = inductive_typ(idx);
        id_typ(&m)
    })
}

fn impossible_id_typ() -> Rc<NegTyp> {
    forall(|idx| {
        Rc::new(NegTyp::Fun(
            existential_typ(),
            Rc::new(NegTyp::Force(inductive_typ(idx))),
        ))
    })
}

#[test]
fn check_id_typ() {
    let ctx = FullContext::default();
    eprintln!("== test1");
    ctx.check_expr(&id_fun(), &id_typ(&unit_typ()));
    eprintln!();
    eprintln!("== test2");
    ctx.check_expr(&id_fun(), &id_typ(&existential_typ()));
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
    let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    ctx.verify(&xi.w);
    assert_eq!(res, inductive_typ(&InnerTerm::Zero.share()));
    // eprintln!();
    // eprintln!("== test2");
    // let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    // ctx.verify(&xi.w);
}
