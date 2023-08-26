#![allow(unused_macros)]

macro_rules! add_tau {
    ($tau:expr; ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        add_tau!($tau; $($($tail)*)?)
    };
    ($tau:expr; ($($l:tt)*) == ($($r:tt)*) $(,$($tail:tt)*)?) => {
        add_tau!($tau; $($($tail)*)?)
    };
    ($tau:expr; $var:ident $(,$($tail:tt)*)?) => {
        $tau.push($crate::refinement::Sort::Nat);
        add_tau!($tau; $($($tail)*)?)
    };
    ($tau:expr;) => {}
}

macro_rules! add_part {
    ($pos:expr; ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        $pos.thunks.push(neg_typ!(($($arg)*) -> ($($ret)*)));
        add_part!($pos; $($($tail)*)?)
    };
    ($pos:expr; ($l:expr) == ($r:expr) $(,$($tail:tt)*)?) => {
        let prop = $crate::refinement::Prop::Eq($l.clone(), $r.clone());
        $pos.prop.push(prop);
        add_part!($pos; $($($tail)*)?)
    };
    ($pos:expr; $var:expr $(,$($tail:tt)*)?) => {
        let fun = $crate::refinement::Fun {
            tau: vec![],
            fun: ::std::rc::Rc::new(move |_| (unqual!(), $crate::refinement::InnerTerm::Zero.share())),
        };
        let measure = $crate::refinement::Measured {
            f_alpha: vec![fun],
            term: $var.clone(),
        };
        $pos.measured.push(measure);
        add_part!($pos; $($($tail)*)?)
    };
    ($pos:expr;) => {}
}

macro_rules! list_var {
    ($($prev:ident)*; ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        list_var!($($prev)*; $($($tail)*)?)
    };
    ($($prev:ident)*; ($l:expr) == ($r:expr) $(,$($tail:tt)*)?) => {
        list_var!($($prev)*; $($($tail)*)?)
    };
    ($($prev:ident)*; $var:ident $(,$($tail:tt)*)?) => {
        list_var!($($prev)* $var; $($($tail)*)?)
    };
    ($($prev:ident)*;) => {
        [$($prev),*]
    }
}

macro_rules! neg_typ {
    (($($arg:tt)*) -> ($($ret:tt)*)) => {{
        #[allow(unused_mut)]
        let mut tau = vec![];
        add_tau!(tau; $($arg)*);
        $crate::refinement::Fun { tau, fun: ::std::rc::Rc::new(|args| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(;$($arg)*) = Vec::leak(args.to_owned()) else { panic!() };
            $crate::refinement::NegTyp {
                arg: unqual!($($arg)*),
                ret: pos_typ!($($ret)*),
            }
        })}
    }};
}

macro_rules! pos_typ {
    ($($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut tau = vec![];
        add_tau!(tau; $($part)*);
        $crate::refinement::Fun { tau, fun: ::std::rc::Rc::new(|args| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(;$($part)*) = Vec::leak(args.to_owned()) else { panic!() };
            unqual!($($part)*)
        })}
    }};
}

macro_rules! unqual {
    ($($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut pos = $crate::refinement::PosTyp {
            measured: vec![],
            thunks: vec![],
            prop: vec![],
        };
        add_part!(pos; $($part)*);
        pos
    }};
}
