use std::{cell::Cell, rc::Rc};

mod subtyp;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Sort;

#[derive(PartialEq, Eq)]
enum Term {
    Var(usize),
}

enum Context<'a> {
    Empty,
    Cons {
        sort: Sort,
        term: Cell<Option<Term>>,
        next: &'a Context<'a>,
    },
}

enum Constraint {
    True,
    And(Rc<Constraint>, Rc<Constraint>),
    Prop(Rc<Prop>),
    PropEq(Rc<Prop>, Rc<Prop>),
    Forall(Sort, Rc<Constraint>),
    EqNegTyp(Rc<NegTyp>, Rc<NegTyp>),
    EqPosTyp(Rc<PosTyp>, Rc<PosTyp>),
    SubNegTyp(Rc<NegTyp>, Rc<NegTyp>),
    SubPosTyp(Rc<PosTyp>, Rc<PosTyp>),
}

#[derive(PartialEq, Eq)]
enum Prop {
    Eq(Rc<Term>, Rc<Term>)
}

#[derive(PartialEq, Eq)]
enum PosTyp {
    Prod(Rc<PosTyp>, Rc<PosTyp>),
    Sum(Rc<PosTyp>, Rc<PosTyp>),
    Refined(Rc<PosTyp>, Rc<Prop>),
    Exists(Sort, Rc<PosTyp>),
    Thunk(Rc<NegTyp>),
    Measured(Rc<SumFunctor>, Algebra, Rc<Term>),
}

#[derive(PartialEq, Eq)]
enum NegTyp {
    Force(Rc<PosTyp>),
    Implies(Rc<Prop>, Rc<NegTyp>),
    Forall(Sort, Rc<NegTyp>),
    Fun(Rc<PosTyp>, Rc<NegTyp>),
}

#[derive(PartialEq, Eq)]
struct SumFunctor {
    sum: Vec<ProdFunctor>,
}

#[derive(PartialEq, Eq)]
struct ProdFunctor {
    prod: Vec<BaseFunctor>,
}

#[derive(PartialEq, Eq)]
enum BaseFunctor {
    Pos(Rc<PosTyp>),
    Id,
}

#[derive(PartialEq, Eq)]
struct SumPattern {
    idx: usize,
    pat: Rc<ProdPattern>,
}

#[derive(PartialEq, Eq)]
struct ProdPattern {
    parts: Vec<BasePattern>,
}

#[derive(PartialEq, Eq)]
enum BasePattern {
    Ignore,
    Var,
    Pack,
}

#[derive(PartialEq, Eq)]
struct Algebra {
    pats: Vec<(SumPattern, Term)>,
}
