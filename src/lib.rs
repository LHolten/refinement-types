#![feature(extract_if)]
#![feature(unique_rc_arc)]
#![feature(never_type)]

use std::{collections::HashMap, rc::Rc};

use refinement::Free;

// mod lpi;
// mod selfref;
// mod typ_check;
// mod untyped;
// mod gadt;
pub mod desugar;
pub mod error;
pub mod parse;
mod refinement;
mod solver;
pub mod uninit_rc;
// mod sequent;

pub struct Struct<T> {
    // forall: Option<FuncNested<T>>,
    map: HashMap<String, Nested<T>>,
}

#[derive(Clone)]
pub struct FuncNested<T> {
    #[allow(clippy::complexity)]
    val: Rc<dyn Fn(&[Free<T>]) -> Struct<T>>,
}

#[derive(Clone)]
pub enum Nested<T> {
    Resource(FuncNested<T>, Vec<Free<T>>),
    Just(T),
}

impl<T> Nested<T> {
    pub fn unwrap_just(&self) -> &T {
        match self {
            Nested::Just(val) => val,
            _ => panic!(),
        }
    }

    pub fn unwrap_more(&self) -> Struct<T> {
        match self {
            Nested::Resource(f, args) => (f.val)(args),
            _ => panic!(),
        }
    }
}
