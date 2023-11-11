use std::rc::Rc;

use crate::refinement::SubContext;

use super::{heap::Heap, Cond, Fun, Lambda, NegTyp, Prop, Sort, Term, Value, Var};

fn id_unit() -> Lambda<Var> {
    parse_lambda!(Var; () => return ())
}

fn id_fun() -> Lambda<Var> {
    parse_lambda!(Var; (val) => return (val))
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
    ctx.clone().check_expr(&id_unit(), &neg_typ!(() -> ()));
    eprintln!("== test2");
    ctx.clone().check_expr(&id_fun(), &neg_typ!((Nat) -> (Nat)));
    eprintln!("== test3");
    ctx.check_expr(&id_fun(), &neg_typ!((a:Nat) -> (b:Nat) where {b == a}));
}

#[test]
fn checkk_id_app() {
    let mut ctx = SubContext::default();
    eprintln!("== test1");
    let typ = ctx.spine(&forall_id_typ(), &inductive_val());
    ctx.check_expr_pos(&parse_expr!(Var; return (0)), &typ);
}

#[test]
fn increment() {
    let ctx = SubContext::default();
    let lamb = parse_lambda! {Var; (ptr) =>
        // let x = ptr.0[0];
        let (x): (v:Nat) where {v == 10} = (10);
        ptr[0] = x;
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
    let lamb = parse_lambda! {Var; (args) =>
        let (_) = args ();
        return ()
    };
    let typ = neg_typ!(
        (func:Nat) where {fn func() -> ()}
            -> ()
    );
    ctx.check_expr(&lamb, &typ);
}

fn terminated(heap: &mut dyn Heap, ptr: &Rc<Term>) {
    fn inner(heap: &mut dyn Heap, args: &[Rc<Term>]) {
        let [ptr] = args else { panic!() };
        let val = heap.owned(ptr, Sort::Nat);

        let not_zero = Rc::new(Prop::LessEq(Rc::new(Term::Nat(1)), val));
        let next_ptr = Rc::new(Term::Add(ptr.clone(), Rc::new(Term::Nat(1))));
        heap.switch(Cond {
            cond: not_zero,
            args: vec![next_ptr],
            func: inner,
        });
    }

    inner(heap, &[ptr.clone()]);
}

#[test]
fn data_typ() {
    let ctx = SubContext::default();
    let lamb = parse_lambda! {Var; args@(ptr, new) =>
        let (val) = ptr[0];
        match val
        /* 0 */ { return () }
        /* 1.. */ {
            ptr[0] = new;
            let (next) = @add(ptr, 1);
            // while terminated(next);
            loop args = (next, new)
        }
    };
    let typ = neg_typ!(
        (ptr:Nat, new:Nat) where {terminated(ptr); 1 <= new}
            -> () where {terminated(ptr)}
    );
    ctx.check_expr(&lamb, &typ);
}

fn option(heap: &mut dyn Heap, ptr: &Rc<Term>) {
    let not_zero = Rc::new(Prop::LessEq(Rc::new(Term::Nat(1)), ptr.clone()));
    heap.switch(Cond {
        cond: not_zero,
        args: vec![ptr.clone()],
        func: inner,
    });

    fn inner(heap: &mut dyn Heap, args: &[Rc<Term>]) {
        let [ptr] = args else { panic!() };
        let _val = heap.owned(ptr, Sort::Nat);
    }
}
