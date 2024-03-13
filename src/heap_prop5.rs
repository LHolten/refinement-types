//! every memory location has a marker, the marker represents an invariant.
//! types associate markers with invariants
//! values are just type pointers (+ mask/lifetime variable?)
//! function arguments and return values associate markers with types.
//! this means that arguments and return values are non-linear, but the heap is linear.
//!
//! functions can extend the origin/mask of a datastructure as long as it does not change the dependencies
//! - if a function has two inputs for example that do not alias, then it can not make them alias
//!
//! i think functions need to be very explicity about what markers they changed or can change
//! - this then makes returning unchanged datastructures automatic?
//! - maybe also return where the new datastructures are inserted?
//!
//! # input
//! - which heap values have which type and are readable
//!     - simplify to everything dereferencable
//! - which heap values are disjoint, so they can be used for allocation
//!     - simplify to everything is disjoint
//! # output
//! - which disjoint heap locations have been allocated and where
//!
//! ```ignore
//! fn alloca(stack: u32, val: u32) -> (new_stack: u32, &'(stack..new_stack) u32)
//!
//! // this is a bit like OnceCell
//! fn snoc(stack: u32, list: &'a List) -> (new_stack: u32, 'a += stack..new_stack)
//! fn cons(stack: u32, list: &'a List) -> (new_stack: u32, &'(a + stack..new_stack) List)
//!
//! // with &mut for uniqueness and destruction
//! // &mut is in and output param, the output can have a different mask
//! // & is non-linear, the output has a mask at least the size of all input lifetimes
//! // - potentially adding stuff that is removed from the &mut
//! fn alloca(stack: &mut [u8], val: u32) -> &u32
//!
//! // inputs are annotated with mut or no mut, outputs with lifetimes
//! // output lifetimes say which non-mut inputs they borrow ('_ is everything, 'static is nothing)
//!
//! // add a new dependency from list to other
//! fn concat(list: &move List, other: &List) -> (&'_ List)
//! // remove other from scope instead
//! fn concat(list: &List, other: &move List)
//! // add item to the front
//! fn cons(alloc: &move [u8], val: u32, list: &List) -> (&'static [u8], &'_ List)
//!
//!
//! // add a new dependency from list to other
//! fn concat(list: box List, other: &List) -> (box List<'_>)
//! // remove other from scope instead, return ref to other
//! fn concat(list: &List, other: box List) -> &'_ List
//! // add item to the front
//! fn cons(alloc: box [u8], val: u32, list: &List) -> (box [u8], box List<'_>)
//!
//! // &mut is a bit like box, but it only invalidates unstable references
//! // an unstable reference is any reference that looks inside an unstable type
//! fn pop(list: &mut List) -> u32
//! ```
//!
//!
//! reading a heap value requires that we know what the value invariant is
//! invariants are always local to a single struct
//! - this means that type parameters can not be refined
//! - if we have a struct where all markers match, we know the invariant
//!
//!
//! ```ignore
//! type test() {
//!     x: &[Test<'a>]
//!     y: &'a u8
//! }
//!
//! (a: &'static T, b: &'a + 'static T) // add a as an origin
//! (xs: BoxU32<'a>, x: &u32) -> xs: BoxU32<'a + 'x>
//!
//! fn push<'a>(xs: Vec<&'a u32>, x: &'a u32) -> Vec<&'a u32>
//!
//! all_unique: [&u32]
//! shared: [&'a u32]
//!
//! ```
//! functions can have lifetime generics
//! - a lifetime generic represents an alias with something in the caller scope
//! - an alias with the caller scope means that heap invariants need to be preserved
//! - otherwise we have ownership and are allowed to change heap invariants
//!
//! a proof mask should be &mut the number of dependencies does not change
//!
//! maybe i can associate a mask with every marker?
//! - this would allow updating all affectected masks
//! - maybe it is not necessary to update any mask, since mask are lower bound
//!
//! So my goal is to make writing these proofs that heap values have a type very easy, it should look close to using any other language.
//! That is why i have these two ways to write such a proof:
//! - By destruction, which is written like accessing fields `foo.bar.bar.stuff`
//! This allows using the unbounded number of proofs in a recursive type definition.
//! - By construction, which uses the familiar struct constructor syntax `Foo { bar: proof1, stuff: proof2 }`
//!
//! Now the difficulty is that sometimes we want to prove stuff that requires reasoning, for example
//!
//! We need some way to guarantee that if a value is accessed from inside a heap_prop,
//! that we also bring all refinements about it into scope.
//! - All refinements of a value must be the same
//!
//!
//! only one type used for &, &mut and Box all together.
//! functions declare whether they
//!
//! two types of references:
//! - owning, can change the type of the memory
//! - borrowing, can not change the type, but can change the values
//!
//! type parametericity:
//! - mutating a Vec<T> can not mutate T
//!
//!
//!
//! # New Idea Yet Again
//! We have a forest of owned trees.
//! Every owned node can also have references into itself.
//! Types divide their owned nodes into regions
//! borrows specify which tree root they are part of + the region.
//! - borrows in a node have to select their own tree.
//! mutating through a borrow allows moving values as long as they stay in the same tree + region

use core::fmt;
use std::{collections::HashSet, rc::Rc, sync::atomic::AtomicUsize};

use crate::refinement::{func_term::FuncTerm, term::Term};

// this is a mask lower bound
// bigger maskes are subtypes
pub struct Lower(FuncTerm);

// this is a mask upper bound
// smaller masks are subtypes
pub struct Upper(FuncTerm);

impl Upper {
    fn or(&self, used: &Upper) -> Upper {
        todo!()
    }

    fn and(&self, mask: &Upper) -> Upper {
        todo!()
    }
}

// to solve the problem of recursive heap properties, we define a new type
// the `rec` field of the scope contains other named props that should hold
pub struct HeapPropNamed {
    name: TypId,

    // second argument is the mask, every read must be inside it
    func_check: Box<dyn Fn(&mut CheckScope)>,
    func_unroll: Box<dyn Fn(&mut UnrollScope)>,
}

/// This represents a location + the parts owned by that location
#[derive(Hash, PartialEq, Eq, Clone, Copy)]
struct RegionId(usize);

impl RegionId {
    pub fn new() -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        Self(ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed))
    }
}

#[derive(Clone)]
struct TypId(Rc<HeapPropNamed>);

impl fmt::Debug for TypId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("TypId").field(&Rc::as_ptr(&self.0)).finish()
    }
}

impl PartialEq for TypId {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

// in order to prove recursive heap properties we need to pass around their proofs
// this type represents the proof of such a property.
#[derive(Clone)]
pub struct TypWithBorrow {
    // the name of the heap prop that this proves
    name: TypId,
    // which owned trees in scope do we borrow
    borrow: HashSet<RegionId>,
}

pub struct Owned {
    typ: TypId,
    reg: RegionId,
}

// this struct will be passed into a heap prop function and check it
// its job is to provide heap values and record which values are used
// it should also use the proofs in the `rec` field to prove recursive calls
struct CheckScope {
    frozen: HashSet<RegionId>,
    params: Params,
}

impl CheckScope {
    pub fn read(&mut self) -> Term {
        self.params.value.remove(0)
    }

    pub fn rec(&mut self, typ: TypWithBorrow) {
        let proof = self.params.rec.remove(0);
        assert_eq!(typ.name, proof.name);

        for b in proof.borrow.difference(&typ.borrow) {
            self.frozen.insert(*b);
        }
    }

    pub fn owned(&mut self, typ: TypId) -> HashSet<RegionId> {
        let own = self.params.rec.remove(0);
        assert_eq!(own.name, typ);

        assert!(self.params.owned.is_superset(&own.borrow));
        own.borrow
    }
}

struct UnrollScope {
    // these will be borrowed by all references
    frozen: HashSet<RegionId>,
    params: Params,
}

#[derive(Default)]
struct Params {
    value: Vec<Term>,
    rec: Vec<TypWithBorrow>,
    owned: HashSet<RegionId>,
}

impl Params {
    fn owned_regions(&self) -> HashSet<RegionId> {
        self.owned.clone()
    }
}

impl UnrollScope {
    pub fn read(&mut self) -> Term {
        let val = Term::fresh("read", 32);
        self.params.value.push(val);
        val
    }

    pub fn rec(&mut self, mut typ: TypWithBorrow) {
        typ.borrow.extend(self.frozen.clone());
        self.params.rec.push(typ);
    }

    pub fn owned(&mut self, mut typ: TypId) -> HashSet<RegionId> {
        let reg = RegionId::new();
        self.params.owned.insert(reg);
        self.params.rec.push(TypWithBorrow {
            name: typ,
            borrow: HashSet::from_iter([reg]),
        });
        HashSet::from_iter([reg])
    }
}

struct Scope {
    outer_scope: RegionId,
    in_scope: HashSet<RegionId>,
}

impl Scope {
    pub fn remove_regions(&mut self, regions: HashSet<RegionId>) {
        assert!(self.in_scope.is_superset(&regions));
        self.in_scope = self.in_scope.difference(&regions).copied().collect();
    }

    // will return what is frozen
    pub fn check(&mut self, typ: TypId, params: Params) -> HashSet<RegionId> {
        self.remove_regions(params.owned);
        let mut check = CheckScope {
            frozen: HashSet::new(),
            params,
        };
        (typ.0.func_check)(&mut check);
        assert!(self.in_scope.is_superset(&check.frozen));
        check.frozen
    }

    pub fn unroll(&mut self, typ: TypId, frozen: HashSet<RegionId>) -> Params {
        let mut unroll = UnrollScope {
            frozen,
            params: Params::default(),
        };
        (typ.0.func_unroll)(&mut unroll);
        self.in_scope.extend(unroll.params.owned);
        unroll.params
    }

    pub fn new(typ: TypId) -> (Self, Params) {
        let outer_scope = RegionId::new();
        let mut scope = Scope {
            outer_scope,
            in_scope: HashSet::new(),
        };
        let params = scope.unroll(typ, HashSet::from_iter([outer_scope]));
        (scope, params)
    }

    pub fn finish(mut self, typ: TypId, params: Params) {
        let frozen = self.check(typ, params);
        assert!(self.in_scope.remove(&self.outer_scope));

        // TODO: This will prevent some leaks
        assert!(self.in_scope.is_empty());
    }

    pub fn apply_func(&mut self, inp: TypId, out: TypId, params: Params) -> Params {
        let frozen = self.check(inp, params);
        let new_params = self.unroll(out, frozen);
        new_params
    }

    pub fn destruct(&mut self, val: TypWithBorrow) -> (Params, Mutating) {
        self.remove_regions(val.borrow);

        let params = self.unroll(val.name, HashSet::new());
        let m = Mutating {
            original: val,
            unfolded: params.owned,
        };

        (params, m)
    }

    pub fn construct(&mut self, params: Params, m: Mutating) {
        // TODO: this will make sure that dereference is stable
        assert!(m.unfolded.is_subset(&params.owned));

        let frozen = self.check(m.original.name, params);
        assert!(frozen.is_empty());

        self.in_scope.extend(m.original.borrow);
    }
}

struct Mutating {
    original: TypWithBorrow,
    unfolded: HashSet<RegionId>,
}
