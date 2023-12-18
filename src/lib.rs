#![feature(extract_if)]
#![feature(unique_rc_arc)]
#![feature(never_type)]

use std::collections::HashMap;

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

#[derive(Clone)]
pub enum Nested<T> {
    More(Option<usize>, HashMap<String, Nested<T>>),
    Just(T),
}

impl<T> Nested<T> {
    pub fn unwrap_just(self) -> T {
        match self {
            Nested::Just(val) => val,
            _ => panic!(),
        }
    }

    pub fn unwrap_more(self) -> HashMap<String, Nested<T>> {
        match self {
            Nested::More(_, more) => more,
            _ => panic!(),
        }
    }
}
