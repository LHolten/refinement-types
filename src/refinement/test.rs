use std::rc::Rc;

use crate::refinement::SubContext;

use super::{heap::Heap, Cond, Fun, Lambda, NegTyp, Prop, Sort, Term, Value, Var};

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
        // let x = ptr.0[0];
        let x: (v:Nat) where {v == 10} = (10);
        ptr.0[0] = x.0;
        return ()
    };
    let typ = neg_typ!(
        (ptr:Nat) where {let old = ptr[0]}
            -> () where {let new = ptr[0]; new == 10}
    );
    ctx.check_expr(&lamb, &typ);
}

#[test]
fn func_arg() {
    let ctx = SubContext::default();
    let lamb = parse_lambda! {Var; args =>
        let _ = args.0 ();
        return ()
    };
    let typ = neg_typ!(
        (func:Nat) where {fn func() -> ()}
            -> ()
    );
    ctx.check_expr(&lamb, &typ);
}

/// zero terminated list type
fn terminated(heap: &mut dyn Heap, is_zero: u32, args: &[Rc<Term>]) {
    let [ptr] = args else { panic!() };
    if is_zero != 0 {
        return;
    }
    let ptr = Rc::new(Term::Add(ptr.clone(), Rc::new(Term::Nat(1))));
    let val = heap.owned(&ptr, Sort::Nat);
    let is_zero = Rc::new(Term::Bool(Rc::new(Prop::Eq(val, Rc::new(Term::Nat(0))))));
    heap.switch(Cond {
        args: vec![is_zero, ptr],
        func: terminated,
    })
}

#[test]
fn data_typ() {
    let ctx = SubContext::default();
    let lamb = parse_lambda! {Var; args =>
        let val = args.0[0];
        match val.0
        {_ => return ()}
        {_ =>
            let x: (v:Nat) where {1 <= v} = (10);
            args.0[0] = x.0;
            // args.0[0] = args.1;
            loop args = (args.0, args.1)
        }
    };
    let typ = neg_typ!(
        (ptr:Nat, new:Nat) where {let val = ptr[0]; terminated(val, ptr); 1 <= new}
            -> () where {let val = ptr[0]; terminated(val, ptr)}
    );
    ctx.check_expr(&lamb, &typ);
}
