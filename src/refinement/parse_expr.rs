#![allow(unused_macros)]

macro_rules! parse_lambda {
    ($ty:ty; $var:pat => $($expr:tt)*) => {
        $crate::refinement::Lambda::new(|tmp: &$ty| {
            let $var = Box::leak(Box::new(tmp.clone()));
            parse_expr!($ty; $($expr)*)})
    }
}

macro_rules! parse_expr {
    ($ty:ty; let $var:pat = $fun:ident.$num:literal ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $var => $($tail)*);
        let local = $crate::refinement::Local($fun.clone(), $num);
        let func = $crate::refinement::Thunk::Local(local);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $var:pat = @$fun:ident ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $var => $($tail)*);
        let builtin = parse_builtin!($fun);
        let func = $crate::refinement::Thunk::Builtin(builtin);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; $var:ident.$num1:tt[0] = $val:ident.$num:tt; $($tail:tt)*) => {{
        let val = parse_value!($ty; $var.$num1, $val.$num);
        let tail = parse_lambda!($ty; _ => $($tail)*);
        let func = $crate::refinement::builtin::Builtin::Write;
        let func = $crate::refinement::Thunk::Builtin(func);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $var:pat = $val:ident.$num:tt[0]; $($tail:tt)*) => {{
        let val = parse_value!($ty; $val.$num);
        let tail = parse_lambda!($ty; $var => $($tail)*);
        let func = $crate::refinement::builtin::Builtin::Read;
        let func = $crate::refinement::Thunk::Builtin(func);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $var:ident: $pos:tt $(where $bound:tt)? = ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $var => $($tail)*);
        let typ = pos_typ!($pos $(where $bound)?);
        let bound = $crate::refinement::BoundExpr::Anno(val, typ);
        $crate::refinement::Expr::<$ty>::Let(bound, tail)
    }};
    ($ty:ty; return ($($val:tt)*)) => {{
        let val = parse_value!($ty; $($val)*);
        $crate::refinement::Expr::Return(val)
    }};
    ($ty:ty; loop $fun:ident = ($($val:tt)*)) => {{
        let val = parse_value!($ty; $($val)*);
        $crate::refinement::Expr::Loop($fun.clone(), val)
    }};
    ($ty:ty; match $fun:ident.$num:literal $({ $($branch:tt)* })* ) => {{
        let branches = vec![$(
            parse_lambda!($ty; $($branch)*)
        ),*];
        let local = $crate::refinement::Local($fun.clone(), $num);
        $crate::refinement::Expr::Match(local, branches)
    }};
}

macro_rules! parse_value {
    ($ty:ty; $($val:tt)*) => {{
        #[allow(unused_mut)]
        let mut val = $crate::refinement::Value::default();
        add_value!($ty; val; $($val)*);
        ::std::rc::Rc::new(val)
    }};
}

macro_rules! parse_builtin {
    (read) => {
        $crate::refinement::builtin::Builtin::Read
    };
    (write) => {
        $crate::refinement::builtin::Builtin::Write
    };
    (add) => {
        $crate::refinement::builtin::Builtin::Add
    };
}

macro_rules! add_value {
    ($ty:ty; $accum:expr; $idx:literal $(,$($tail:tt)*)?) => {
        $accum.inj.push($crate::refinement::Inj::Just($idx));
        add_value!($ty; $accum; $($($tail)*)?)
    };
    ($ty:ty; $accum:expr; $var:ident.$num:literal $(,$($tail:tt)*)?) => {
        let local = $crate::refinement::Local($var.clone(), $num);
        $accum.inj.push($crate::refinement::Inj::Var(local));
        add_value!($ty; $accum; $($($tail)*)?)
    };
    ($ty:ty; $accum:expr; { $($branch:tt)* } $(,$($tail:tt)*)?) => {
        let lambda = parse_lambda!($ty; $($branch)*);
        $accum.thunk.push($crate::refinement::Thunk::Just(lambda));
        add_value!($ty; $accum; $($($tail)*)?)
    };
    ($ty:ty; $accum:expr;)  => {};
}
