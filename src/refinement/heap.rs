use std::{collections::HashMap, rc::Rc};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::ast::Bool;

use crate::solver::ctx;

use super::{func_term::FuncTerm, term::Term, Forall, Maybe, Resource, SubContext};

#[derive(Clone)]
pub enum New {
    Normal(Normal),
    Partial(Partial),
}

#[derive(Clone)]
struct Normal {
    resource: Resource,
    mask: FuncTerm,
    value: FuncTerm,
}

#[derive(Clone)]
struct Partial {
    // named: Named,
    arg_sizes: Vec<(u32, String)>,
    map: Rc<dyn Fn(&[Term]) -> HashMap<String, New>>,
    // _map: HashMap<String, Rc<dyn Fn(&[Term]) -> New<V>>>
}

#[derive(Clone, Copy)]
pub enum MaskOp {
    Distinct,
    Includes,
}

impl New {
    pub fn fresh_args(&self) -> Vec<Term> {
        match self {
            Self::Normal(normal) => normal.resource.make_fresh_args(),
            Self::Partial(partial) => partial
                .arg_sizes
                .iter()
                .map(|(size, prefix)| Term::fresh(prefix, *size))
                .collect(),
        }
    }

    fn mask_diff(&mut self, mut need: New) {
        if let (New::Normal(have), New::Normal(need)) = (&mut *self, &need) {
            have.mask = have.mask.difference(&need.mask);
        } else {
            let (have, need) = (self.unfold(), need.unfold());
            let (old_have, old_need) = (have.clone(), need.clone());
            have.map = Rc::new(move |args| {
                let mut have = (old_have.map)(args);
                let need = (old_need.map)(args);
                for (k, v) in need {
                    have.get_mut(&k).unwrap().mask_diff(v);
                }
                have
            });
        }
    }

    fn copy_value(mut self, need: &mut New) {
        if let (New::Normal(have), New::Normal(need)) = (&self, &mut *need) {
            need.value = have.value.clone();
        } else {
            let (have, need) = (self.unfold(), need.unfold());
            let (old_have, old_need) = (have.clone(), need.clone());
            need.map = Rc::new(move |args| {
                let mut have = (old_have.map)(args);
                let mut need = (old_need.map)(args);
                for (k, v) in &mut need {
                    have.remove(k).unwrap().copy_value(v);
                }
                need
            });
        }
    }

    fn append(&mut self, mut new: New) {
        if let (New::Normal(have), New::Normal(new)) = (&mut *self, &new) {
            have.mask = have.mask.or(&new.mask);
            have.value = new.mask.ite(&new.value, &have.value)
        } else {
            let (have, new) = (self.unfold(), new.unfold().clone());
            let old_have = have.clone();
            have.map = Rc::new(move |args| {
                let (mut have, mut new) = ((old_have.map)(args), (new.map)(args));
                have.iter_mut().for_each(|(k, v)| {
                    v.mask_diff(new.remove(k).unwrap());
                });
                have
            });
        }
    }

    pub fn mask_cmp(mut self, mut need: New, op: MaskOp) -> Bool<'static> {
        let idx = self.fresh_args();
        if let (New::Normal(have), New::Normal(need)) = (&self, &need) {
            let have_mask = have.mask.apply_bool(&idx);
            let need_mask = need.mask.apply_bool(&idx);

            match op {
                MaskOp::Distinct => need_mask.xor(&have_mask),
                MaskOp::Includes => need_mask.implies(&have_mask),
            }
        } else {
            let (have, need) = (self.unfold(), need.unfold());
            let mut have = (have.map)(&idx);
            let need = (need.map)(&idx);

            need.into_iter()
                .map(|(k, v)| have.remove(&k).unwrap().mask_cmp(v, op))
                .fold(Bool::from_bool(ctx(), true), |a, b| a & b)
        }
    }

    pub fn is_empty(self) -> Bool<'static> {
        let idx = self.fresh_args();
        match self {
            New::Normal(have) => have.mask.apply_bool(&idx).not(),
            New::Partial(have) => {
                let have = (have.map)(&idx);
                have.into_values()
                    .map(|v| v.is_empty())
                    .fold(Bool::from_bool(ctx(), true), |a, b| a & b)
            }
        }
    }

    pub fn value_equal(mut self, mut need: New) -> Bool<'static> {
        let idx = need.fresh_args();
        if let (New::Normal(have), New::Normal(need)) = (&self, &need) {
            let need_mask = need.mask.apply_bool(&idx);
            let have_value = have.value.apply(&idx);
            let need_value = need.value.apply(&idx);
            need_mask.implies(&need_value.eq(&have_value).to_bool())
        } else {
            let (have, need) = (self.unfold(), need.unfold());
            let mut have = (have.map)(&idx);
            let need = (need.map)(&idx);

            need.into_iter()
                .map(|(k, v)| have.remove(&k).unwrap().value_equal(v))
                .fold(Bool::from_bool(ctx(), true), |a, b| a & b)
        }
    }

    pub fn bool_and(&mut self, cond: Term) {
        match self {
            New::Normal(normal) => normal.mask = normal.mask.and(&FuncTerm::always(cond)),
            New::Partial(partial) => {
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

    pub fn with_proj(mut self, proj: &Proj) -> Self {
        for (attr, expected) in proj.parts.clone().into_iter().rev() {
            let old = self.clone();
            self = New::Partial(Partial {
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

    pub fn remove_proj(mut self, proj: &Proj) -> Self {
        for (attr, expected) in &proj.parts {
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
                        let mut heap = HeapProduce {
                            scope_value: maybe.value.apply(args),
                            new_scope: HashMap::new(),
                        };
                        (named.typ.fun)(&mut heap, args).unwrap();

                        let cond = maybe.mask.apply(args);
                        heap.new_scope
                            .values_mut()
                            .for_each(|v| v.bool_and(cond.clone()));
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

pub(super) struct HeapConsume<'a> {
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

impl<'a> std::ops::DerefMut for HeapConsume<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
    }
}

impl<'a> std::ops::Deref for HeapConsume<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

pub(super) struct HeapProduce {
    // the value of the resource we are expanding inside
    pub scope_value: Term,
    pub new_scope: HashMap<String, New>,
}

impl New {
    pub fn get_byte(&self, idx: &[Term]) -> Term {
        let New::Normal(forall) = self else {
            panic!();
        };
        assert!(forall.resource == Resource::Owned);
        forall.value.apply(idx)
    }
}

pub trait Heap {
    fn exactly(&mut self, name: &str, part: New) -> Result<(), ConsumeErr>;
    fn forall(&mut self, name: &str, forall: Forall) -> Result<New, ConsumeErr>;

    fn maybe(&mut self, name: &str, switch: Maybe) -> Result<New, ConsumeErr> {
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

impl Heap for HeapConsume<'_> {
    fn exactly(&mut self, name: &str, mut need: New) -> Result<(), ConsumeErr> {
        let original = need.clone();
        let trans = self.translate[name].clone();
        self.remove(&trans, &mut need);
        let eq = original.value_equal(need);
        assert!(self.assume.is_always_true(eq));
        Ok(())
    }

    fn forall(&mut self, name: &str, need: Forall) -> Result<New, ConsumeErr> {
        // TODO: optimization: skip everything if cond is impossible
        let mut need = New::Normal(Normal {
            resource: need.resource,
            mask: need.mask,
            value: FuncTerm::Unused,
        });
        let trans = self.translate[name].clone();
        self.remove(&trans, &mut need);
        Ok(need)
    }
}

impl Heap for HeapProduce {
    fn exactly(&mut self, name: &str, part: New) -> Result<(), ConsumeErr> {
        let existing = self.new_scope.insert(name.to_owned(), part);
        assert!(existing.is_none());
        Ok(())
    }

    fn forall(&mut self, name: &str, have: Forall) -> Result<New, ConsumeErr> {
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
        let part = New::Normal(Normal {
            resource: have.resource,
            mask: have.mask,
            value,
        });

        let existing = self.new_scope.insert(name.to_owned(), part.clone());
        assert!(existing.is_none());
        Ok(part)
    }
}

impl SubContext {
    // self is updated to remove the mask
    // need is updated to set the value (mask may be overriden)
    fn remove(&mut self, trans: &Translate, need: &mut New) {
        match trans {
            Translate::Slice(proj) => {
                let need_proj = need.clone().with_proj(proj);
                let have = &mut self.forall.get_mut(&proj.first).unwrap();
                let verify = have.clone().mask_cmp(need_proj.clone(), MaskOp::Includes);
                assert!(self.assume.is_always_true(verify));

                have.mask_diff(need_proj);
                have.clone().remove_proj(proj).copy_value(need);
            }
            Translate::Build(args, build) => {
                let args = args.clone();
                let need = need.unfold();
                // TODO: check that we indeed only need for args
                let mut need_one = (need.map)(&args);

                for (k, v) in &mut need_one {
                    self.remove(&build[k], v);
                }
                *need = Partial {
                    arg_sizes: need.arg_sizes.clone(),
                    map: Rc::new(move |idx| {
                        let cond = FuncTerm::exactly(&args).apply(idx);
                        let mut new = need_one.clone();
                        new.values_mut().for_each(|v| v.bool_and(cond.clone()));
                        new
                    }),
                }
            }
        }
    }

    // self is updated to include both the mask and value of `new`
    fn append(&mut self, trans: &Translate, mut new: New) {
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
