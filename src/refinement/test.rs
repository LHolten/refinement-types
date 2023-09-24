use std::rc::Rc;

use crate::refinement::{heap::HeapConsume, SubContext};

use super::{Fun, Lambda, NegTyp, Sort, Term, Value, Var};

fn id_unit() -> Lambda<Var> {
    parse_lambda!(Var; _val => return ())
}

fn id_fun() -> Lambda<Var> {
    parse_lambda!(Var; val => return (val.0))
}

fn inductive_val() -> Rc<Value<Var>> {
    parse_value!(Var; 0)
}

fn forall_id_typ() -> Fun<NegTyp> {
    neg_typ!((a:Nat) -> (b:Nat) where {b == a})
}

#[test]
fn check_id_typ() {
    let ctx = SubContext::default();
    eprintln!("== test1");
    ctx.check_expr(&id_unit(), &neg_typ!(() -> ()));
    eprintln!();
    eprintln!("== test2");
    ctx.check_expr(&id_fun(), &neg_typ!((Nat) -> (Nat)));
    eprintln!();
    eprintln!("== test3");
    ctx.check_expr(&id_fun(), &neg_typ!((a:Nat) -> (b:Nat) where {b == a}));
    eprintln!();
    // eprintln!("== test4");
    // ctx.check_expr(&id_fun(), &impossible_id_typ())
}

#[test]
fn checkk_id_app() {
    let mut ctx = SubContext::default();
    eprintln!("== test1");
    let res = ctx.spine(&forall_id_typ(), &inductive_val());

    let mut heap = HeapConsume(&mut ctx);
    let res = (res.fun)(&[Rc::new(Term::UVar(100, Sort::Nat))], &mut heap);
    eprintln!("res = {:?}", res);
    // assert_eq!((res.fun)(&[]).0, inductive_typ(&InnerTerm::Zero.share()));
    // eprintln!();
    // eprintln!("== test2");
    // let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    // ctx.verify(&xi.w);
}
