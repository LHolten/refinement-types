#![allow(dead_code)]

use std::{fmt::Debug, ops::Deref, rc::Rc};

#[macro_use]
mod parse_typ;
#[macro_use]
mod parse_expr;

mod builtin;
mod eval;
mod subtyp;
#[cfg(test)]
mod test;
mod typing;
mod unroll;
mod util;
mod verify;

pub use typing::Var;

use self::{builtin::Builtin, util::Opaque};

// pub fn zero() -> Rc<Term> {
//     thread_local!(static ZERO: Rc<Term> = Rc::new(Term::Nat(0)));
//     ZERO.with(Rc::clone)
// }

// pub fn prop_true() -> Rc<Prop> {
//     thread_local!(static TRUE: Rc<Prop> = Rc::new(Prop::True));
//     TRUE.with(Rc::clone)
// }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sort {
    Bool,
    Nat,
}

type RsrFun = dyn FnOnce(&mut Heap) -> Vec<Rc<Term>>;

#[non_exhaustive]
#[derive(PartialEq, Eq, Debug, Clone)]
enum Term {
    UVar(usize, Sort),
    Nat(usize),
    /// The value read from a pointer
    Owned(Rc<Term>),
    /// Sum type based on a descriminator
    Cond(Rc<Term>),
}

#[derive(Clone, Debug, Default)]
struct Heap {
    alloc: Vec<Resource>,
    prop: Vec<Prop>,
}

impl Heap {
    /// all uses of `alloc` are recorded as resources
    fn owned(&mut self, ptr: &Rc<Term>, tau: Sort) -> Rc<Term> {
        let res = Term::Owned(ptr.clone());
        self.alloc.push(Resource::Single {
            location: ptr.clone(),
            tau,
        });
        Rc::new(res)
    }

    /// using switch will make resources locked behind the value of a term
    fn switch(&mut self, val: Rc<Term>, branches: Vec<Rc<RsrFun>>) -> Rc<Term> {
        let res = branches.into_iter().map(Opaque).collect();
        self.alloc.push(Resource::Cond(val.clone(), res));
        Rc::new(Term::Cond(val))
    }

    fn assert_eq(&mut self, x: &Rc<Term>, y: &Rc<Term>) {
        self.prop.push(Prop::Eq(x.clone(), y.clone()));
    }
}

/// a single resource
#[derive(Clone, Debug)]
enum Resource {
    Single { location: Rc<Term>, tau: Sort },
    Cond(Rc<Term>, Vec<Opaque<RsrFun>>),
}

#[derive(Default)]
enum Context {
    #[default]
    Empty,
    Assume {
        phi: Prop,
        next: Rc<Context>,
    },
}

impl Debug for Context {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut res = Vec::new();
        let mut this = self;
        while let Self::Assume { phi, next } = this {
            this = next;
            res.push(phi);
        }
        f.debug_list().entries(res.iter().rev()).finish()
    }
}

#[derive(Clone, Default)]
struct SubContext {
    univ: usize,
    assume: Rc<Context>,
    heap: Heap,
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>),
    MeasureEq(Measure, [Rc<Term>; 2]),
    True,
}
// PosType is product like, it can contain any number of items
#[derive(PartialEq, Eq, Debug, Default, Clone)]
struct PosTyp {
    thunks: Vec<Fun<NegTyp>>,
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct Measure {
    // alpha: Rc<dyn Fn(usize, &[Rc<Term>]) -> Rc<Term>>,
}

#[derive(PartialEq, Eq, Debug)]
struct NegTyp {
    arg: PosTyp,
    ret: Fun<PosTyp>,
}

// stores resources
struct Owned(Rc<dyn Fn(Rc<Term>) -> Rc<Term>>);

#[allow(clippy::type_complexity)]
struct Fun<T> {
    tau: Vec<Sort>,
    fun: Rc<dyn Fn(&[Rc<Term>], &mut Heap) -> T>,
}

struct WithHeap<T> {
    heap: Heap,
    typ: T,
}

impl<T> Deref for WithHeap<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.typ
    }
}

impl<T> Fun<T> {
    fn with_terms(&self, terms: &[Rc<Term>]) -> WithHeap<T> {
        assert_eq!(self.tau.len(), terms.len());
        let mut heap = Heap::default();
        WithHeap {
            typ: (self.fun)(terms, &mut heap),
            heap,
        }
    }
}

impl<T> Clone for Fun<T> {
    fn clone(&self) -> Self {
        Self {
            tau: self.tau.clone(),
            fun: self.fun.clone(),
        }
    }
}

impl<T> PartialEq for Fun<T> {
    fn eq(&self, _other: &Self) -> bool {
        panic!()
    }
}

impl<T> Eq for Fun<T> {}

impl<T> Debug for Fun<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("MyFun").finish()
    }
}

pub struct Solved<T> {
    terms: Vec<Rc<Term>>,
    inner: T,
}

impl<T> Deref for Solved<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<V> Lambda<V> {
    pub fn inst(&self, var: &V) -> Expr<V> {
        (self.0)(var)
    }

    pub fn new<F: Fn(&V) -> Expr<V> + 'static>(fun: F) -> Self {
        Self(Rc::new(fun))
    }
}

#[allow(clippy::type_complexity)]
struct Lambda<V>(Rc<dyn Fn(&V) -> Expr<V>>);

impl<V> Clone for Lambda<V> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

struct Value<V> {
    thunk: Vec<Thunk<V>>,
    inj: Vec<Inj<V>>,
}

impl<V> Default for Value<V> {
    fn default() -> Self {
        Self {
            thunk: Default::default(),
            inj: Default::default(),
        }
    }
}

enum Inj<V> {
    Just(usize),
    // second argument is projection
    Var(V, usize),
}

enum Thunk<V> {
    Just(Lambda<V>),
    Var(V, usize),
}

enum FuncRef<V> {
    Local(V, usize),
    Builtin(Builtin),
}

enum Expr<V> {
    /// construct a value and return it
    Return(Rc<Value<V>>),

    /// execute an expression and bind the result in the continuation
    Let(BoundExpr<V>, Lambda<V>),

    /// match on some inductive type and choose a branch
    Match(V, usize, Vec<Lambda<V>>),

    /// loop back to an assigment
    Loop(V, Rc<Value<V>>),
}

enum BoundExpr<V> {
    /// apply a function to some arguments
    App(FuncRef<V>, Rc<Value<V>>),

    Anno(Rc<Value<V>>, Fun<PosTyp>),
}

// - Make Prod type any length and povide projections
// - Remove the Sum type
// - Functors do not destruct tuples
// - Remove EqualTerms
// - Use deep embedding for qualified types
// - Flatten types
// - No longer return constraints, verified eagerly now
