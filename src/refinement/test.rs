use std::rc::Rc;

use super::{Expr, FullContext, NegTyp, PosTyp, ProdFunctor, Sort, Term, Value};

fn var(x: usize) -> Rc<Term> {
    Rc::new(Term::LVar(x))
}

fn id_fun() -> Expr {
    Expr::Lambda(Rc::new(Expr::Return(Rc::new(Value::Var(0, vec![])))))
}

fn unit_typ() -> Rc<PosTyp> {
    Rc::new(PosTyp::Prod(vec![]))
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
        vec![(Rc::new(ProdFunctor { prod: vec![] }), Rc::new(Term::Zero))],
        idx.clone(),
    ))
}

fn existential_typ() -> Rc<PosTyp> {
    let m = inductive_typ(&var(0));
    Rc::new(PosTyp::Exists(Sort::Nat, m))
}

fn forall_id_typ() -> Rc<NegTyp> {
    let m = inductive_typ(&var(0));
    Rc::new(NegTyp::Forall(Sort::Nat, id_typ(&m)))
}

fn impossible_id_typ() -> Rc<NegTyp> {
    Rc::new(NegTyp::Forall(
        Sort::Nat,
        Rc::new(NegTyp::Fun(
            existential_typ(),
            Rc::new(NegTyp::Force(inductive_typ(&var(0)))),
        )),
    ))
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
    assert_eq!(res, inductive_typ(&Rc::new(Term::Zero)));
    // eprintln!();
    // eprintln!("== test2");
    // let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    // ctx.verify(&xi.w);
}
