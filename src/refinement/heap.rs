use std::{collections::HashMap, hash::Hash, rc::Rc};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use super::{func_term::FuncTerm, term::Term, Forall, Maybe, Resource, SubContext};

#[derive(Clone)]
pub struct CtxForall {
    resource: Resource,
    mask: NewTerm,
    value: NewTerm,
}

#[derive(Clone)]
pub enum NewTerm {
    Normal(Normal),
    Partial(Partial),
}

#[derive(Clone)]
struct Normal {
    resource: Resource,
    value: FuncTerm,
}

#[derive(Clone)]
struct Partial {
    arg_sizes: Vec<(u32, String)>,
    map: Rc<dyn Fn(&[Term]) -> HashMap<String, NewTerm>>,
}

impl NewTerm {
    pub fn apply(&self, proj: &Idx) -> Term {
        let mut curr = self.clone();
        for (args, attr) in &proj.parts {
            let curr = (curr.unfold().map)(&args).remove(attr).unwrap();
        }
        let NewTerm::Normal(curr) = curr else {
            panic!()
        };
        curr.value.apply(&proj.last)
    }

    pub fn ite(&self, then: &Self, other: &Self) -> Self {
        if let (NewTerm::Normal(cond), NewTerm::Normal(then), NewTerm::Normal(other)) =
            (self, then, other)
        {
            NewTerm::Normal(Normal {
                resource: cond.resource,
                value: cond.value.ite(&then.value, &other.value),
            })
        } else {
            let cond = self.unfold().clone();
            let then = then.unfold().clone();
            let other = other.unfold().clone();

            let map = Rc::new(move |args| {
                let mut other = (other.map)(args);
                let then = (then.map)(args);
                for (k, v) in (cond.map)(args) {
                    other.insert(k, v.ite(&then[&k], &other[&k]));
                }
                other
            });

            NewTerm::Partial(Partial {
                arg_sizes: cond.arg_sizes.clone(),
                map,
            })
        }
    }

    pub fn fresh_args(&self) -> impl Iterator<Item = Idx> {
        match self {
            Self::Normal(normal) => {
                vec![Idx {
                    parts: vec![],
                    last: normal.resource.make_fresh_args(),
                }]
            }
            Self::Partial(partial) => {
                let args: Vec<Term> = partial
                    .arg_sizes
                    .iter()
                    .map(|(size, prefix)| Term::fresh(prefix, *size))
                    .collect();
                (partial.map)(&args)
                    .into_iter()
                    .flat_map(|(k, v)| {
                        let args = args.clone();
                        v.fresh_args().map(move |mut rest| {
                            rest.parts.insert(0, (args.clone(), k.clone()));
                            rest
                        })
                    })
                    .collect()
            }
        }
        .into_iter()
    }

    // pub fn make_suitable(&self, projs: impl Iterator<Item = Proj>) -> impl Iterator<Item = Proj> {
    //     projs.flat_map(|proj| {
    //         self.remove_proj(&proj)
    //             .fresh_args()
    //             .map(|new| proj.concat(new))
    //     })
    // }

    pub fn bool_and(&mut self, cond: Term) {
        match self {
            NewTerm::Normal(normal) => normal.mask = normal.mask.and(&FuncTerm::always(cond)),
            NewTerm::Partial(partial) => {
                let old = partial.clone();
                *partial = Partial {
                    arg_sizes: old.arg_sizes,
                    map: Rc::new(move |args| {
                        let mut new = (old.map)(args);
                        new.values_mut().for_each(|v| v.bool_and(cond.clone()));
                        new
                    }),
                }
            }
        }
    }

    pub fn with_proj(mut self, proj: &Idx) -> Self {
        for (attr, expected) in proj.parts.clone().into_iter().rev() {
            let old = self.clone();
            self = NewTerm::Partial(Partial {
                arg_sizes: expected
                    .iter()
                    .map(|x| (x.get_size(), "".to_owned()))
                    .collect(),
                map: Rc::new(move |args| {
                    let mut new = old.clone();
                    new.bool_and(FuncTerm::exactly(&expected).apply(&args));
                    [(attr.clone(), new)].into_iter().collect()
                }),
            });
        }
        self
    }

    pub fn remove_proj(mut self, proj: &Idx) -> Self {
        for (attr, expected) in &proj.0 {
            let inner = self.unfold();
            self = (inner.map)(&expected).remove(attr).unwrap();
        }
        self
    }

    // get a partial from a maybe or partial resource
    pub fn unfold(&mut self) -> &mut Partial {
        match self {
            Self::Normal(maybe) => {
                let maybe = maybe.clone();

                let Resource::Named(named) = maybe.resource else {
                    panic!("can only access attributes of named resources")
                };

                let once = Partial {
                    arg_sizes: named.typ.tau.clone(),
                    map: Rc::new(move |args| {
                        let mut heap = HeapUnfold {
                            value: maybe.value.apply(args),
                            cond: maybe.mask.apply(args),
                            out: HashMap::new(),
                        };
                        (named.typ.fun)(&mut heap, args).unwrap();

                        heap.new_scope
                    }),
                };

                *self = Self::Partial(once);
                let Self::Partial(once) = self else {
                    unreachable!()
                };
                once
            }
            Self::Partial(partial) => partial,
        }
    }
}

pub(super) struct HeapRemove<'a> {
    pub inner: &'a mut SubContext,
    pub translate: HashMap<String, Translate>,
}

#[derive(Clone)]
pub enum Translate {
    Slice(Proj),
    Build(Vec<Term>, HashMap<String, Translate>),
}

impl Translate {
    pub fn simple(name: String) -> Self {
        Self::Slice(Proj {
            first: name,
            parts: vec![],
        })
    }
}

#[derive(Clone)]
pub struct Proj {
    pub first: String,
    pub parts: Vec<(String, Vec<Term>)>,
}

#[derive(Clone)]
pub struct Idx {
    parts: Vec<(Vec<Term>, String)>,
    last: Vec<Term>,
}

impl<'a> std::ops::DerefMut for HeapRemove<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'a> std::ops::Deref for HeapRemove<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

pub(super) struct HeapProduce {
    // the value of the resource we are expanding inside
    pub scope_value: Term,
    pub new_scope: HashMap<String, CtxForall>,
}

impl NewTerm {
    pub fn get_byte(&self, idx: &[Term]) -> Term {
        let NewTerm::Normal(forall) = self else {
            panic!();
        };
        assert!(forall.resource == Resource::Owned);
        forall.value.apply(idx)
    }
}

pub trait Heap {
    fn exactly(&mut self, name: &str, part: CtxForall) -> Result<(), ConsumeErr>;
    fn forall(&mut self, name: &str, forall: Forall) -> Result<NewTerm, ConsumeErr>;

    fn maybe(&mut self, name: &str, switch: Maybe) -> Result<NewTerm, ConsumeErr> {
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

impl Heap for HeapRemove<'_> {
    fn exactly(&mut self, name: &str, mut need: CtxForall) -> Result<(), ConsumeErr> {
        let trans = self.translate[name].clone();
        let have_value = self.remove(&trans, &need.mask);

        for proj in need.mask.fresh_args() {
            let need_mask = need.mask.apply(&proj);
            let value_have = have_value.apply(&proj);
            let value_need = need.value.apply(&proj);
            let verify = need_mask.implies(&value_have.eq(&value_need));
            assert!(self.assume.is_always_true(verify.to_bool()));
        }

        Ok(())
    }

    fn forall(&mut self, name: &str, need: Forall) -> Result<NewTerm, ConsumeErr> {
        // TODO: optimization: skip everything if cond is impossible
        let need = NewTerm::Normal(Normal {
            resource: need.resource,
            value: need.mask,
        });
        let trans = self.translate[name].clone();
        let result = self.remove(&trans, &need);
        Ok(result)
    }
}

impl Heap for HeapProduce {
    fn exactly(&mut self, name: &str, part: CtxForall) -> Result<(), ConsumeErr> {
        let existing = self.new_scope.insert(name.to_owned(), part);
        assert!(existing.is_none());
        Ok(())
    }

    fn forall(&mut self, name: &str, have: Forall) -> Result<NewTerm, ConsumeErr> {
        let func = have.resource.associated_func();
        // we want to make sure that expanding the same resource twice gives the same result
        // this is why the values inside the forall are keyed by the parent value
        // TODO: optimization: this scope_value might not need to be "leveled" and could be replaced by the one at the root
        let scope_value = self.scope_value.clone();
        let value = FuncTerm::new(move |args| {
            let mut new_args = vec![scope_value.clone()];
            new_args.extend_from_slice(args);
            func.apply(&new_args)
        });
        let part = CtxForall {
            resource: have.resource,
            mask: NewTerm::Normal(Normal {
                resource: have.resource,
                value: have.mask,
            }),
            value: NewTerm::Normal(Normal {
                resource: have.resource,
                value,
            }),
        };

        let existing = self.new_scope.insert(name.to_owned(), part.clone());
        assert!(existing.is_none());
        Ok(part.value)
    }
}

impl SubContext {
    // self is updated to remove the mask
    // post: self mask includes the mask indices
    fn remove(&mut self, trans: &Translate, need_mask: &NewTerm) -> NewTerm {
        match trans {
            Translate::Slice(proj) => {
                let need_proj = need_mask.clone().with_proj(proj);
                let have = self.forall.get_mut(&proj.first).unwrap();

                for args in need_mask.fresh_args() {
                    let need_idx = need_mask.apply(&args);
                    let have_idx = have.mask.apply(&args);
                    let verify = need_idx.implies(&have_idx).to_bool();
                    assert!(self.assume.is_always_true(verify));
                }

                have.mask = need_mask.ite(&NewTerm::always(Term::bool(false)), &have.mask);
                have.value
            }
            Translate::Build(args, build) => {
                let args = args.clone();
                let need = need_mask.unfold();
                // TODO: check that we indeed only need for args
                let mut need_one = (need.map)(&args);

                let mut out = HashMap::new();
                for (k, v) in &mut need_one {
                    let val = self.remove(&build[k], v);
                    out.insert(k.clone(), val);
                }

                NewTerm::Partial(Partial {
                    arg_sizes: need.arg_sizes.clone(),
                    map: Rc::new(move |idx| out.clone()),
                })
            }
        }
    }

    // self is updated to include both the mask and value of `new`
    fn append(&mut self, trans: &Translate, mut new: CtxForall) {
        match trans {
            Translate::Slice(proj) => {
                let new_proj = new.with_proj(proj);
                let have = self.forall.get_mut(&proj.first).unwrap();
                let verify = have.clone().mask_cmp(new_proj.clone(), MaskOp::Distinct);
                assert!(self.assume.is_always_true(verify));
                have.append(new_proj);
            }
            Translate::Build(args, build) => {
                let new = new.unfold();
                // TODO: check that we indeed only have new for args
                let new_one = (new.map)(args);
                for (k, v) in new_one {
                    self.append(&build[&k], v);
                }
            }
        }
    }
}

struct HeapUnfold {
    cond: Term,
    value: Term,
    out: HashMap<String, CtxForall>,
}

impl Heap for HeapUnfold {
    fn exactly(&mut self, name: &str, mut part: CtxForall) -> Result<(), ConsumeErr> {
        part.mask.bool_and(self.cond);
        self.out.insert(name.to_owned(), part);
        Ok(())
    }

    fn forall(&mut self, name: &str, have: Forall) -> Result<NewTerm, ConsumeErr> {
        let func = have.resource.associated_func();
        let scope_value = self.value.clone();
        let value = FuncTerm::new(move |args| {
            let mut new_args = vec![scope_value.clone()];
            new_args.extend_from_slice(args);
            func.apply(&new_args)
        });
        let mut part = CtxForall {
            resource: have.resource,
            mask: NewTerm::Normal(Normal {
                resource: have.resource,
                value: have.mask,
            }),
            value: NewTerm::Normal(Normal {
                resource: have.resource,
                value,
            }),
        };
        part.mask.bool_and(self.cond);
        self.out.insert(name.to_owned(), part);
        Ok(part.value)
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
