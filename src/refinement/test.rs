use std::rc::Rc;

use super::{Expr, FullContext, NegTyp, PosTyp, ProdFunctor, Sort, Term, Value};

fn id_fun() -> Value {
    Value::Thunk(Rc::new(Expr::Lambda(Rc::new(Expr::Return(Rc::new(
        Value::Var(0, vec![]),
    ))))))
}

fn unit_typ() -> Rc<PosTyp> {
    Rc::new(PosTyp::Prod(vec![]))
}

fn id_typ(arg: &Rc<PosTyp>) -> PosTyp {
    PosTyp::Thunk(Rc::new(NegTyp::Fun(
        arg.clone(),
        Rc::new(NegTyp::Force(arg.clone())),
    )))
}

fn inductive_typ() -> Rc<PosTyp> {
    let m = Rc::new(PosTyp::Measured(
        vec![(Rc::new(ProdFunctor { prod: vec![] }), Rc::new(Term::Zero))],
        Rc::new(Term::LVar(0)),
    ));
    Rc::new(PosTyp::Exists(Sort::Nat, m))
}

#[test]
fn check_id_typ() {
    let ctx = FullContext::default();
    let cons = ctx.check_value(&id_fun(), &id_typ(&unit_typ()));
    ctx.verify(&cons.w);

    let cons = ctx.check_value(&id_fun(), &id_typ(&inductive_typ()));
    ctx.verify(&cons.w);
}
