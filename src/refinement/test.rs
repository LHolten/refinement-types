use std::rc::Rc;

use crate::refinement::SubContext;

use super::{
    heap::{BoolFuncTerm, Heap},
    Cond, Forall, Fun, Lambda, NegTyp, Term, Value, Var,
};

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

fn terminated_inner(heap: &mut dyn Heap, args: &[Term]) {
    let [ptr] = args else { panic!() };
    let val = heap.owned_byte(ptr);

    let not_zero = val.not_zero();
    let next_ptr = ptr.add(&Term::nat(1, 32));
    heap.switch(Cond {
        cond: not_zero,
        args: vec![next_ptr],
        func: terminated_inner,
    });
}

fn terminated(heap: &mut dyn Heap, ptr: &Term) {
    terminated_inner(heap, &[ptr.clone()]);
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
            unpack terminated_inner(next);
            loop args = (next, new)
        }
    };
    let typ = neg_typ!(
        (ptr:Nat, new:Nat) where {terminated(ptr); 1 <= new}
            -> () where {terminated(ptr)}
    );
    ctx.check_expr(&lamb, &typ);
}

fn option(heap: &mut dyn Heap, ptr: &Term) {
    let not_zero = ptr.not_zero();
    heap.switch(Cond {
        cond: not_zero,
        args: vec![ptr.clone()],
        func: inner,
    });

    fn inner(heap: &mut dyn Heap, args: &[Term]) {
        let [ptr] = args else { panic!() };
        let _val = heap.owned_byte(ptr);
    }
}

fn mem(heap: &mut dyn Heap, args: &[Term]) {
    let [ptr] = args else { panic!() };
    heap.owned_byte(ptr);
}

fn array(heap: &mut dyn Heap, from: &Term, len: &Term) {
    let end = from.add(len);
    let from = from.clone();
    heap.assert(from.ule(&end));
    heap.forall(Forall {
        func: mem,
        mask: BoolFuncTerm::new(move |args| {
            let [ptr] = args else { panic!() };
            from.ule(ptr).to_bool() & ptr.ult(&end).to_bool()
        }),
        arg_size: vec![32],
    });
}

#[test]
fn array_test() {
    let ctx = SubContext::default();
    let lamb = parse_lambda! {Var; args@(ptr, len, new) =>
        match len
        /* 0 */ { return () }
        /* 1.. */ {
            unpack mem(ptr);
            ptr[0] = new;
            pack mem(ptr);

            let (new_ptr) = @add(ptr, 1);
            let (new_len) = @add(len, -1);
            loop args = (new_ptr, new_len, new)
        }
    };
    let typ = neg_typ!(
        (ptr:Nat, len:Nat, new:Nat) where {array(ptr, len)}
            -> () where {array(ptr, len)}
    );
    ctx.check_expr(&lamb, &typ);
}
