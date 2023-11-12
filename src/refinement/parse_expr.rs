#![allow(unused_macros)]

macro_rules! parse_lambda {
    ($ty:ty; $($name:ident@)? ($($var:pat),*) => $($expr:tt)*) => {
        $crate::refinement::Lambda::new(|tmp: &$ty| {
            #[allow(unused_variables)]
            let tmp = &*Box::leak(Box::new(tmp.clone()));
            $(let $name = tmp;)?

            #[allow(unused_variables)]
            let i = 0;
            $(
                let $var = Box::leak(Box::new($crate::refinement::Local(tmp.clone(), i)));
                #[allow(unused_variables)]
                let i = i + 1;
            )*
            parse_expr!($ty; $($expr)*)})
    }
}

macro_rules! parse_expr {
    ($ty:ty; let $($name:ident@)? ($($var:tt),*) = $fun:ident ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $($name@)? ($($var),*) => $($tail)*);
        let func = $crate::refinement::Thunk::Local($fun.clone());
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $($name:ident@)? ($($var:tt),*) = @$fun:ident ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $($name@)? ($($var),*) => $($tail)*);
        let builtin = parse_builtin!($fun);
        let func = $crate::refinement::Thunk::Builtin(builtin);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; $var:ident[0] = $val:ident; $($tail:tt)*) => {{
        let val = parse_value!($ty; $var, $val);
        let tail = parse_lambda!($ty; () => $($tail)*);
        let func = $crate::refinement::builtin::Builtin::Write;
        let func = $crate::refinement::Thunk::Builtin(func);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $($name:ident@)? ($($var:tt),*) = $val:ident[0]; $($tail:tt)*) => {{
        let val = parse_value!($ty; $val);
        let tail = parse_lambda!($ty; $($name@)? ($($var),*) => $($tail)*);
        let func = $crate::refinement::builtin::Builtin::Read;
        let func = $crate::refinement::Thunk::Builtin(func);
        let bound = $crate::refinement::BoundExpr::App(func, val);
        $crate::refinement::Expr::Let(bound, tail)
    }};
    ($ty:ty; let $($name:ident@)? ($($var:tt),*): $pos:tt $(where $bound:tt)? = ($($val:tt)*); $($tail:tt)*) => {{
        let val = parse_value!($ty; $($val)*);
        let tail = parse_lambda!($ty; $($name@)? ($($var),*) => $($tail)*);
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
    ($ty:ty; match $val:ident $({ $($branch:tt)* })* ) => {{
        let branches = vec![$(
            parse_lambda!($ty; () => $($branch)*)
        ),*];
        $crate::refinement::Expr::Match($val.clone(), branches)
    }};
    ($ty:ty; unpack $fun:ident ($($val:expr),*); $($tail:tt)*) => {{
        let tail = parse_expr!($ty; $($tail)*);
        $crate::refinement::Expr::Unpack($fun, vec![$($val.clone()),*], ::std::rc::Rc::new(tail))
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
    ($ty:ty; $accum:expr; $var:ident $(,$($tail:tt)*)?) => {
        $accum.inj.push($crate::refinement::Inj::Var($var.clone()));
        add_value!($ty; $accum; $($($tail)*)?)
    };
    ($ty:ty; $accum:expr; { $($branch:tt)* } $(,$($tail:tt)*)?) => {
        let lambda = parse_lambda!($ty; $($branch)*);
        $accum.thunk.push($crate::refinement::Thunk::Just(lambda));
        add_value!($ty; $accum; $($($tail)*)?)
    };
    ($ty:ty; $accum:expr;)  => {};
}
