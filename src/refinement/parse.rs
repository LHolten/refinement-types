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
    ($fun:expr; ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        add_tau!($fun; $($($tail)*)?)
    };
    ($fun:expr; ($($l:tt)*) == ($($r:tt)*) $(,$($tail:tt)*)?) => {
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

macro_rules! parse_term {
    ($var:ident.$num:literal) => {
        $var.get_term($num)
    };
    ($t:expr) => {
        $t.clone()
    };
}

macro_rules! add_part {
    ($heap:ident; $pos:tt; ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
        $pos.thunks.push(neg_typ!(($($arg)*) -> ($($ret)*)));
        add_part!($heap; $pos; $($($tail)*)?)
    };
    ($heap:ident; $pos:tt; ($($l:tt)*) == ($($r:tt)*) $(,$($tail:tt)*)?) => {
        $heap.assert_eq(parse_term!($($l)*), parse_term!($($r)*));
        add_part!($heap; $pos; $($($tail)*)?)
    };
    ($heap:ident; $pos:tt; $var:ident:Nat $(,$($tail:tt)*)?) => {
        add_part!($heap; $pos; $($($tail)*)?)
    };
    ($heap:ident; $pos:tt; Nat $(,$($tail:tt)*)?) => {
        add_part!($heap; $pos; $($($tail)*)?)
    };
    ($heap:ident; $pos:tt;) => {}
}

macro_rules! list_var {
    ($($prev:pat)* => ($($arg:tt)*) -> ($($ret:tt)*) $(,$($tail:tt)*)?) => {
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
    (($($arg:tt)*) -> ($($ret:tt)*)) => {{
        #[allow(unused_mut, unused_variables)]
        let mut fun = $crate::refinement::Fun {
            tau: vec![],
            fun: ::std::rc::Rc::new(|args, heap| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(=> $($arg)*) = Vec::leak(args.to_owned()) else { panic!() };
            $crate::refinement::NegTyp {
                arg: unqual!(heap; $($arg)*),
                ret: pos_typ!($($ret)*),
            }
        })};
        add_tau!(fun; $($arg)*);
        fun
    }};
}

macro_rules! pos_typ {
    ($($part:tt)*) => {{
        #[allow(unused_mut, unused_variables)]
        let mut fun = $crate::refinement::Fun {
            tau: vec![],
            fun: ::std::rc::Rc::new(|args, heap| {
            // NOTE: this is a memory leak, but it is only for tests
            let list_var!(=> $($part)*) = Vec::leak(args.to_owned()) else { panic!() };
            unqual!(heap; $($part)*)
        })};
        add_tau!(fun; $($part)*);
        fun
    }};
}

/// a postive type from only functions and props
macro_rules! unqual {
    ($heap:ident; $($part:tt)*) => {{
        #[allow(unused_mut)]
        let mut pos = $crate::refinement::PosTyp {
            thunks: vec![],
        };
        add_part!($heap; pos; $($part)*);
        pos
    }};
}
