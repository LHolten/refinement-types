#![allow(unused_macros)]

/// Enum syntax:
/// ```
/// enum NatList() {
///     0 => Nil {},
///     n => Cons {
///         move val = n[0], // read a u32
///         move next_ptr = n[1], // read another u32 with offset
///         let next = NatList(next_ptr),
///     }
/// }
///
/// impl NatList {
///     const fn len(self) {
///         match self {
///             Nil => return 0,
///             Cons{ next, .. } => {
///                 return next.len() + 1;
///             }
///         }
///     }
///
///     // count how often an element occurs in a list
///     const fn count(self, x) {
///         match self {
///             Nil => return 0,
///             Cons{ next, val, .. } => {
///                 let count = next.count(x);
///                 if val == x {
///                     return count + 1;
///                 } else {
///                     return count;
///                 }
///             }
///         }
///     }
/// }
///
/// type eq_elem(l: NatList, r: NatList) {
///     await l.len() == r.len();
///     for x in 0.. {
///         await l.count(x) == r.count(x);
///     }
/// }
///
/// fn Clone(ptr: Nat) where {
///     let ref list = NatList(ptr);
/// } -> (ptr: Nat) where {
///     let new_list = NatList(ptr);
///     new_list = (i: Nat) -> (n: Cons) where {
///         n.val = list[i].val
///     }
/// }
/// ```

macro_rules! add_tau {
    (@start $fun:expr; ($($tail:tt)*)) => {
        add_tau!($fun; $($tail)*)
    };
    ($fun:expr; $arg:tt -> $ret:tt $(,$($tail:tt)*)?) => {
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr; $l:tt == $r:tt $(,$($tail:tt)*)?) => {
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr; $var:ident:Nat $(,$($tail:tt)*)?) => {
        $fun.tau.push($crate::refinement::Sort::Nat);
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr; Nat $(,$($tail:tt)*)?) => {
        $fun.tau.push($crate::refinement::Sort::Nat);
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr;) => {}
}

macro_rules! list_var {
    (@start ($($tail:tt)*)) => {
        list_var!(=> $($tail)*)
    };
    ($($prev:pat)* => $arg:tt -> $ret:tt $(,$($tail:tt)*)?) => {
        list_var!($($prev)* => $($($tail)*)?)
    };
    ($($prev:pat)* => ($l:expr) == ($r:expr) $(,$($tail:tt)*)?) => {
        list_var!($($prev)* => $($($tail)*)?)
    };
    ($($prev:pat)* => $var:ident:$ty:tt $(,$($tail:tt)*)?) => {
        list_var!($($prev)* $var => $($($tail)*)?)
    };
    ($($prev:pat)* => $ty:tt $(,$($tail:tt)*)?) => {
        list_var!($($prev)* _ => $($($tail)*)?)
    };
    ($($prev:pat)* =>) => {
        [$($prev),*]
    }
}

macro_rules! neg_typ {
    ($arg:tt -> $($ret:tt)*) => {
        neg_typ!($arg where {} -> $($ret)*)
    };
    ($arg:tt where $arg_bound:tt -> $($ret:tt)*) => {{
        #[allow(unused_mut, unused_variables)]
        let mut fun = $crate::refinement::Fun {
            tau: vec![],
            fun: ::std::rc::Rc::new(|args, heap| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(@start $arg) = Vec::leak(args.to_owned()) else { panic!() };
            bounds!(@start heap; $arg_bound);
            $crate::refinement::NegTyp {
                arg: crate::refinement::PosTyp,
                ret: pos_typ!($($ret)*),
            }
        })};
        add_tau!(@start fun; $arg);
        fun
    }};
}

macro_rules! pos_typ {
    ($part:tt) => {
        pos_typ!($part where {})
    };
    ($part:tt where $bound:tt) => {{
        #[allow(unused_mut, unused_variables)]
        let mut fun = $crate::refinement::Fun {
            tau: vec![],
            fun: ::std::rc::Rc::new(|args, heap| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(@start $part) = Vec::leak(args.to_owned()) else { panic!() };
            bounds!(@start heap; $bound);
            $crate::refinement::PosTyp
        })};
        add_tau!(@start fun; $part);
        fun
    }};
}

/// a postive type from only functions
macro_rules! funcs {
    ($part:tt) => {{
        #[allow(unused_mut)]
        let mut pos = $crate::refinement::PosTyp {
            thunks: vec![],
        };
        add_part!(@start pos; $part);
        pos
    }};
}

macro_rules! bounds {
    (@start $heap:ident; {$($tail:tt)*}) => {
        bounds!($heap; $($tail)*);
    };
    ($heap:ident; $l:tt == $r:tt $(;$($tail:tt)*)?) => {
        $heap.assert_eq(term!($l), term!($r));
        bounds!($heap; $($($tail)*)?);
    };
    ($heap:ident; let $var:pat = $val:ident[$idx:literal] $(;$($tail:tt)*)?) => {
        let tmp = $heap.owned($val, $crate::refinement::Sort::Nat);
        let $var = Box::leak(Box::new(tmp));
        bounds!($heap; $($($tail)*)?);
    };
    ($heap:ident; fn $val:ident $arg:tt $(where $bound:tt)? -> $ret:tt $(where $bound2:tt)? $(;$($tail:tt)*)?) => {
        $heap.func($val, neg_typ!($arg $(where $bound)? -> $ret $(where $bound2)?));
        bounds!($heap; $($($tail)*)?);
    };
    ($heap:ident; $func:ident ($($arg:tt),*)) => {
        $heap.switch($crate::refinement::Cond{
            args: vec![$($arg.clone()),*],
            func: $func,
        });
    };
    ($heap:ident;) => {}
}

macro_rules! term {
    ($name:ident) => {
        $name
    };
    ($val:literal) => {
        &::std::rc::Rc::new($crate::refinement::Term::Nat($val))
    };
}
