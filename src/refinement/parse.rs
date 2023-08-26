#![allow(unused_macros)]

macro_rules! add_tau {
    ($fun:expr; ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr; ($($l:tt)*) == ($($r:tt)*) $(,$($tail:tt)*)?) => {
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr; $var:pat $(,$($tail:tt)*)?) => {
        $fun.tau.push($crate::refinement::Sort::Nat);
        let fun = $crate::refinement::Fun {
            tau: vec![],
            measured: vec![],
            fun: ::std::rc::Rc::new(move |_| (unqual!(), $crate::refinement::InnerTerm::Zero.share())),
        };
        $fun.measured.push($crate::refinement::Measured {
            f_alpha: vec![fun],
        });
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr;) => {}
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
    ($pos:expr; $var:pat $(,$($tail:tt)*)?) => {
        add_part!($pos; $($($tail)*)?)
    };
    ($pos:expr;) => {}
}

macro_rules! list_var {
    ($($prev:pat)* => ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        list_var!($($prev)* => $($($tail)*)?)
    };
    ($($prev:pat)* => ($l:expr) == ($r:expr) $(,$($tail:tt)*)?) => {
        list_var!($($prev)* => $($($tail)*)?)
    };
    ($($prev:pat)* => $var:pat $(,$($tail:tt)*)?) => {
        list_var!($($prev)* $var => $($($tail)*)?)
    };
    ($($prev:pat)* =>) => {
        [$($prev),*]
    }
}

macro_rules! neg_typ {
    (($($arg:tt)*) -> ($($ret:tt)*)) => {{
        #[allow(unused_mut)]
        let mut fun = $crate::refinement::Fun {
            tau: vec![],
            measured: vec![],
            fun: ::std::rc::Rc::new(|args| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(=> $($arg)*) = Vec::leak(args.to_owned()) else { panic!() };
            $crate::refinement::NegTyp {
                arg: unqual!($($arg)*),
                ret: pos_typ!($($ret)*),
            }
        })};
        add_tau!(fun; $($arg)*);
        fun
    }};
}

macro_rules! pos_typ {
    ($($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut fun = $crate::refinement::Fun {
            tau: vec![],
            measured: vec![],
            fun: ::std::rc::Rc::new(|args| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(=> $($part)*) = Vec::leak(args.to_owned()) else { panic!() };
            unqual!($($part)*)
        })};
        add_tau!(fun; $($part)*);
        fun
    }};
}

macro_rules! unqual {
    ($($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut pos = $crate::refinement::PosTyp {
            thunks: vec![],
            prop: vec![],
        };
        add_part!(pos; $($part)*);
        pos
    }};
}
