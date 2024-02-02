use std::{collections::HashMap, rc::Rc};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use super::{func_term::FuncTerm, term::Term, Forall, Maybe, Named, Resource, SubContext};

#[derive(Clone)]
pub enum NewTerm {
    Normal(Normal),
    Partial(Partial),
}

#[derive(Clone)]
pub struct Normal {
    pub value: FuncTerm,
    pub mask: FuncTerm,
}

#[derive(Clone)]
pub enum ValueOnly {
    Normal(FuncTerm),
    Partial(Rc<dyn Fn(&[Term]) -> HashMap<String, ValueOnly>>),
}

impl ValueOnly {
    pub fn apply(&self, idx: &[Term]) -> SingleValue {
        match self {
            ValueOnly::Normal(normal) => SingleValue::Just(normal.apply(idx)),
            ValueOnly::Partial(partial) => SingleValue::Map(partial(idx)),
        }
    }
}

#[derive(Clone)]
pub enum SingleValue {
    Just(Term),
    Map(HashMap<String, ValueOnly>),
}

#[derive(Clone)]
pub struct Partial {
    map: Rc<dyn Fn(&[Term]) -> HashMap<String, NewTerm>>,
}

impl NewTerm {
    pub fn value(&self) -> ValueOnly {
        match self {
            NewTerm::Normal(normal) => ValueOnly::Normal(normal.value),
            NewTerm::Partial(partial) => ValueOnly::Partial(Rc::new(|args| {
                (partial.map)(args)
                    .into_iter()
                    .map(|(k, v)| (k, v.value()))
                    .collect()
            })),
        }
    }
}

impl ValueOnly {
    pub fn bool_and(&self, func: FuncTerm) -> NewTerm {
        match self {
            ValueOnly::Normal(normal) => NewTerm::Normal(Normal {
                value: normal.clone(),
                mask: func,
            }),
            ValueOnly::Partial(partial) => {
                let old = partial.clone();
                NewTerm::Partial(Partial {
                    map: Rc::new(move |args| {
                        let mut new = old(args);
                        let func = FuncTerm::always(func.apply(args));
                        new.into_iter()
                            .map(|(k, v)| (k, v.bool_and(func)))
                            .collect()
                    }),
                })
            }
        }
    }

    pub fn unfold(&self, named: Named) -> Rc<dyn Fn(&[Term]) -> HashMap<String, ValueOnly>> {
        match self {
            ValueOnly::Partial(partial) => partial.clone(),
            ValueOnly::Normal(func) => Rc::new(|idx| {
                let mut heap = HeapUnfold {
                    cond: Term::bool(true),
                    value: func.apply(idx),
                    out: HashMap::new(),
                };
                (named.typ.fun)(&mut heap, idx).unwrap();
                heap.out.into_iter().map(|(k, v)| (k, v.value())).collect()
            }),
        }
    }
}

#[derive(Clone, Default)]
pub struct Proj {
    pub parts: Vec<(String, Vec<Term>)>,
}

#[derive(Clone)]
pub struct Idx {
    parts: Vec<(Vec<Term>, String)>,
    last: Vec<Term>,
}

pub enum HeapOp {
    Remove,
    Append,
}

pub(super) struct HeapRemove {
    pub old_scope: HashMap<String, NewTerm>,
}

impl NewTerm {
    pub fn get_byte(&self, idx: &[Term]) -> Term {
        let NewTerm::Normal(forall) = self else {
            panic!();
        };
        forall.value.apply(idx)
    }
}

pub trait Heap {
    fn exactly(&mut self, name: &str, forall: Forall, value: ValueOnly) -> Result<(), ConsumeErr>;
    fn forall(&mut self, name: &str, forall: Forall) -> Result<ValueOnly, ConsumeErr>;

    fn maybe(&mut self, name: &str, switch: Maybe) -> Result<ValueOnly, ConsumeErr> {
        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
        };
        self.forall(name, forall)
    }
    fn assert(&mut self, name: &str, phi: Term) -> Result<(), ConsumeErr> {
        let switch = Maybe {
            resource: Resource::Impossible,
            args: vec![],
            cond: phi.bool_not(),
        };

        self.maybe(name, switch)?;
        Ok(())
    }
}

impl Heap for HeapRemove {
    fn exactly(&mut self, name: &str, forall: Forall, _value: ValueOnly) -> Result<(), ConsumeErr> {
        self.forall(name, forall)?;
        Ok(())
    }

    fn forall(&mut self, name: &str, need: Forall) -> Result<ValueOnly, ConsumeErr> {
        match &mut self.old_scope[name] {
            NewTerm::Normal(normal) => {
                normal.mask = normal.mask.difference(&need.mask);
            }
            NewTerm::Partial(partial) => {
                partial.map = Rc::new(|idx| {
                    let mut heap = HeapRemove {
                        old_scope: (partial.map)(idx),
                    };
                    let Resource::Named(named) = need.resource else {
                        panic!()
                    };
                    (named.typ.fun)(&mut heap, &idx).unwrap();
                    heap.old_scope
                })
            }
        }
        Ok(self.old_scope[name].value())
    }
}

pub(super) struct HeapCheck {
    pub op: HeapOp,
    pub old_scope: HashMap<String, NewTerm>,
    pub verify: Term,
}

impl Heap for HeapCheck {
    fn exactly(&mut self, name: &str, forall: Forall, value: ValueOnly) -> Result<(), ConsumeErr> {
        let have_value = self.forall(name, forall)?;

        todo!();
        // for proj in forall.fresh_args() {
        //     let need_mask = need.mask.apply(&proj);
        //     let value_have = have_value.apply(&proj);
        //     let value_need = need.value.apply(&proj);
        //     let verify = need_mask.implies(&value_have.eq(&value_need));
        //     assert!(self.assume.is_always_true(verify.to_bool()));
        // }

        Ok(())
    }

    fn forall(&mut self, name: &str, forall: Forall) -> Result<ValueOnly, ConsumeErr> {
        let idx = forall.resource.make_fresh_args();
        let pre = forall.mask.apply(&idx);
        let post = match &self.old_scope[name] {
            NewTerm::Normal(normal) => match self.op {
                HeapOp::Remove => normal.mask.apply(&idx),
                HeapOp::Append => normal.mask.apply(&idx).bool_not(),
            },
            NewTerm::Partial(partial) => {
                let mut heap = HeapCheck {
                    op: self.op,
                    old_scope: (partial.map)(&idx),
                    verify: Term::bool(true),
                };
                let Resource::Named(named) = forall.resource else {
                    panic!()
                };
                (named.typ.fun)(&mut heap, &idx)?;
                heap.verify
            }
        };
        self.verify = self.verify.bool_and(&pre.implies(&post));
        // TODO: when HeapOp::Append, i need to generate these values?
        match self.op {
            HeapOp::Remove => Ok(self.old_scope[name].value()),
            HeapOp::Append => todo!(),
        }
    }
}

struct HeapIte {
    cond: Term,
    value: SingleValue,
    out: HashMap<String, NewTerm>,
}

impl Heap for HeapIte {
    fn exactly(&mut self, name: &str, forall: Forall, value: ValueOnly) -> Result<(), ConsumeErr> {
        let mask = forall.mask.and(&FuncTerm::always(self.cond));
        let mut other = self.out[name];
        self.out[name] = if let (ValueOnly::Normal(value), NewTerm::Normal(normal)) = (value, other)
        {
            NewTerm::Normal(Normal {
                value: mask.ite(&value, &normal.value),
                mask: mask.or(&normal.mask),
            })
        } else {
            let Resource::Named(named) = forall.resource else {
                panic!()
            };
            let other = match other {
                NewTerm::Normal(normal) => Partial {
                    map: Rc::new(|idx| {
                        let mut heap = HeapUnfold {
                            cond: normal.mask.apply(idx),
                            value: normal.value.apply(idx),
                            out: HashMap::new(),
                        };
                        (named.typ.fun)(&mut heap, idx).unwrap();
                        heap.out
                    }),
                },
                NewTerm::Partial(partial) => partial,
            };

            NewTerm::Partial(Partial {
                map: Rc::new(|idx| {
                    let mut heap = HeapIte {
                        cond: mask.apply(idx),
                        value: value.apply(idx),
                        out: (other.map)(idx),
                    };
                    (named.typ.fun)(&mut heap, idx).unwrap();
                    heap.out
                }),
            })
        };

        Ok(())
    }

    fn forall(&mut self, name: &str, have: Forall) -> Result<ValueOnly, ConsumeErr> {
        let resource = &have.resource;
        let value = match self.value {
            SingleValue::Just(scope_value) => ValueOnly::Normal(resource.expand(scope_value)),
            SingleValue::Map(map) => map[name],
        };

        self.exactly(name, have, value)?;
        Ok(value)
    }
}

impl Resource {
    pub fn expand(&self, scope_value: Term) -> FuncTerm {
        let func = self.associated_func();
        FuncTerm::new(move |args| {
            let mut new_args = vec![scope_value.clone()];
            new_args.extend_from_slice(args);
            func.apply(&new_args)
        })
    }
}

impl SubContext {
    pub fn remove<T>(&mut self, mut new: impl FnOnce(&mut dyn Heap) -> T) -> T {
        let mut heap = HeapCheck {
            op: HeapOp::Remove,
            old_scope: self.forall,
            verify: Term::bool(true),
        };
        let res = new(&mut heap);
        assert!(self.assume.is_always_true(heap.verify.to_bool()));

        let mut heap = HeapRemove {
            old_scope: self.forall,
        };
        let res = new(&mut heap);
        self.forall = heap.old_scope;
        res
    }

    pub fn append<T>(&mut self, mut new: impl Fn(&mut dyn Heap) -> T) -> T {
        let mut heap = HeapCheck {
            op: HeapOp::Append,
            old_scope: self.forall,
            verify: Term::bool(true),
        };
        let res = new(&mut heap);
        assert!(self.assume.is_always_true(heap.verify.to_bool()));

        let mut heap = HeapIte {
            cond: Term::bool(true),
            value: SingleValue::Just(Term::fresh_uninterpreted()),
            out: self.forall,
        };
        let res = new(&mut heap);
        self.forall = heap.out;
        res
    }
}

struct HeapUnfold {
    cond: Term,
    value: Term,
    out: HashMap<String, NewTerm>,
}

impl Heap for HeapUnfold {
    fn exactly(&mut self, name: &str, forall: Forall, value: ValueOnly) -> Result<(), ConsumeErr> {
        let part = value.bool_and(forall.mask.and(&FuncTerm::always(self.cond)));
        self.out.insert(name.to_owned(), part);
        Ok(())
    }

    fn forall(&mut self, name: &str, have: Forall) -> Result<ValueOnly, ConsumeErr> {
        let func = have.resource.associated_func();
        let scope_value = self.value.clone();
        let value = FuncTerm::new(move |args| {
            let mut new_args = vec![scope_value.clone()];
            new_args.extend_from_slice(args);
            func.apply(&new_args)
        });
        let value = ValueOnly::Normal(value);
        self.exactly(name, have, value.clone());
        Ok(value)
    }
}

#[derive(Debug, Diagnostic, Error)]
pub enum ConsumeErr {
    #[error("Number of args is not equal")]
    NumArgs,

    #[error("The resource does not always exist")]
    MissingResource {
        #[label = "The resource"]
        resource: Option<SourceSpan>,
        #[help]
        help: String,
    },

    #[error("The assertion is not always true")]
    InvalidAssert {
        #[label = "The assertion"]
        assert: Option<SourceSpan>,
        #[help]
        help: String,
    },
}
