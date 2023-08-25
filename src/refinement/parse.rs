#![allow(unused_macros)]

macro_rules! add_tau {
    ($tau:expr; ($($arg:tt)*) -> ($($ret:tt)*) $(,$tail:tt)*) => {
        add_tau!($tau; $($tail),*)
    };
    ($tau:expr; $var:ident $(,$tail:tt)*) => {
        $tau.push($crate::refinement::Sort::Nat);
        add_tau!($tau; $($tail),*)
    };
    ($tau:expr;) => {}
}

macro_rules! add_part {
    ($inj:expr; $thunk:expr; ($($arg:tt)*) -> ($($ret:tt)*) $(,$tail:tt)*) => {
        $thunk.push(neg_typ!($($tts)*));
        add_part!($inj; $thunk; $($tail),*)
    };
    ($inj:expr; $thunk:expr; $var:expr $(,$tail:tt)*) => {
        let fun = $crate::refinement::Fun {
            tau: vec![],
            fun: ::std::rc::Rc::new(move |_| ((unqual!(), $crate::refinement::InnerTerm::Zero.share()), vec![])),
        };
        let measure = $crate::refinement::Measured {
            f_alpha: vec![fun],
            term: $var.clone(),
        };
        $inj.push(measure);
        add_part!($inj; $thunk; $($tail),*)
    };
    ($inj:expr; $thunk:expr;) => {}
}

macro_rules! list_var {
    ($($prev:ident)*; ($($arg:tt)*) -> ($($ret:tt)*) $($rem:tt)*) => {
        list_var!($($prev)*; $($rem)*)
    };
    ($($prev:ident)*; $var:ident $($rem:tt)*) => {
        list_var!($($prev)* $var; $($rem)*)
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
            let list_var!(;$($arg)*) = args else { panic!() };
            let neg = $crate::refinement::NegTyp {
                arg: unqual!($($arg)*),
                ret: pos_typ!($($ret)*),
            };
            (neg, vec![])
        }) }
    }};
}

macro_rules! pos_typ {
    ($($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut tau = vec![];
        add_tau!(tau; $($part)*);
        $crate::refinement::Fun { tau, fun: ::std::rc::Rc::new(|args| {
            let list_var!(;$($part)*) = args else { panic!() };
            let pos = unqual!($($part)*);
            (pos, vec![])
        }) }
    }};
}

macro_rules! unqual {
    ($($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut pos = $crate::refinement::PosTyp {
            measured: vec![],
            thunks: vec![],
        };
        add_part!(pos.measured; pos.thunks; $($part)*);
        pos
    }};
}
