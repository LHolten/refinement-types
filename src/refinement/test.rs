use std::rc::Rc;

use crate::refinement::SubContext;

use super::{Fun, Lambda, NegTyp, Value, Var};

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
    eprintln!("== test2");
    ctx.check_expr(&id_fun(), &neg_typ!((Nat) -> (Nat)));
    eprintln!("== test3");
    ctx.check_expr(&id_fun(), &neg_typ!((a:Nat) -> (b:Nat) where {b == a}));
}

#[test]
fn checkk_id_app() {
    let mut ctx = SubContext::default();
    eprintln!("== test1");
    let typ = ctx.spine(&forall_id_typ(), &inductive_val());

    let (res, _ctx) = ctx.extract(&typ);
    eprintln!("res.terms = {:?}", res.terms);
    // assert_eq!((res.fun)(&[]).0, inductive_typ(&InnerTerm::Zero.share()));
    // eprintln!();
    // eprintln!("== test2");
    // let (res, xi) = ctx.spine(&forall_id_typ(), &[inductive_val()]);
    // ctx.verify(&xi.w);
}

#[test]
fn increment() {
    let ctx = SubContext::default();
    let lamb = parse_lambda! {Var; ptr =>
        let x = ptr.0[0];
        // let x: (Nat) = (10);
        ptr.0[0] = x.0;
        return ()
    };
    let typ = neg_typ!(
        (ptr:Nat) where {let old = ptr[0]}
            -> () where {let new = ptr[0]; new == old}
    );
    ctx.check_expr(&lamb, &typ);
}
