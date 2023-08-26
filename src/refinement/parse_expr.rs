#![allow(unused_macros)]

macro_rules! parse_lambda {
    ($ty:ty; $var:ident => $($expr:tt)*) => {
        $crate::refinement::Lambda::new(|tmp: &$ty| {
            let $var = Box::leak(Box::new(tmp.clone()));
            parse_expr!($ty; $($expr)*)})
    }
}

macro_rules! parse_expr {
    ($ty:ty; let $var:ident = $fun:ident.$num:literal ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $var => $($tail)*);
        let bound = $crate::refinement::BoundExpr::App($fun, $num, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $var:ident: ($($neg:tt)*) = ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_lambda!($ty; $var => $($val)*);
        let tail = parse_lambda!($ty; $var => $($tail)*);
        let typ = unqual!($($neg)*);
        let bound = $crate::refinement::BoundExpr::Anno(val, typ.thunks);
        $crate::refinement::Expr::<$ty>::Let(bound, tail)
    }};
    ($ty:ty; return ($($val:tt)*)) => {{
        let val = parse_value!($ty; $($val)*);
        $crate::refinement::Expr::Return(val)
    }};
    ($ty:ty; tail $fun:ident.$num:literal ($($val:tt)*)) => {{
        let val = parse_value!($ty; $($val)*);
        $crate::refinement::Expr::Tail($fun.clone(), $num, val)
    }};
    ($ty:ty; match $fun:ident.$num:literal $({ $($branch:tt)* })* ) => {{
        let branches = vec![$(
            parse_lambda!($ty; $($branch)*)
        ),*];
        $crate::refinement::Expr::Match($fun.clone(), $num, branches)
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

macro_rules! add_value {
    ($ty:ty; $accum:expr; $idx:literal($($val:tt)*) $(,$($tail:tt)*)?) => {
        let val = parse_value!($ty; $($val)*);
        $accum.inj.push($crate::refinement::Inj::Just($idx, val));
        add_value!($ty; $accum; $(,$($tail:tt)*)?)
    };
    ($ty:ty; $accum:expr; $var:ident.$num:literal $(,$($tail:tt)*)?) => {
        $accum.inj.push($crate::refinement::Inj::Var($var.clone(), $num));
        add_value!($ty; $accum; $(,$($tail:tt)*)?)
    };
    ($ty:ty; $accum:expr; { $($branch:tt)* } $(,$($tail:tt)*)?) => {
        let lambda = parse_lambda!($ty; $($branch)*);
        $accum.thunk.push($crate::refinement::Thunk::Just(lambda));
        add_value!($ty; $accum; $(,$($tail:tt)*)?)
    };
    ($ty:ty; $accum:expr;)  => {};
}
