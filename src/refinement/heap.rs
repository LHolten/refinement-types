use std::{cmp::min, collections::HashMap, iter::zip, rc::Rc};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::refinement::{typing::zip_eq, Removed};

use super::{func_term::FuncTerm, term::Term, Forall, Maybe, Resource, SubContext};

#[derive(Clone)]
pub struct ForPart {
    pub resource: Resource,
    pub mask: FuncTerm,
    pub value: FuncTerm,
}

#[derive(Clone)]
pub struct MaybePart {
    pub resource: Resource,
    pub args: Vec<Term>,
    pub cond: Term,
    pub value: Term,
}

#[derive(Clone)]
pub struct OncePart {
    pub resource: Resource,
    pub args: Vec<Term>,
    pub map: HashMap<String, NewPart>,
}

// keeps track of a linear resource that is in scope
#[derive(Clone)]
pub enum NewPart {
    Forall(ForPart),
    Maybe(MaybePart),
    Partial(OncePart),
}

impl NewPart {
    pub fn resource(&self) -> &Resource {
        match self {
            NewPart::Forall(forall) => &forall.resource,
            NewPart::Partial(once) => &once.resource,
        }
    }

    pub fn mask(&self) -> FuncTerm {
        match self {
            NewPart::Forall(forall) => forall.mask.clone(),
            NewPart::Partial(once) => FuncTerm::exactly(&once.args),
        }
    }

    pub fn args(&self) -> Option<&[Term]> {
        match self {
            NewPart::Forall(_) => None,
            NewPart::Maybe(maybe) => Some(&maybe.args),
            NewPart::Partial(once) => Some(&once.args),
        }
    }

    // get a partial from a maybe or partial resource
    pub fn unfold(&mut self) -> &mut OncePart {
        match self {
            NewPart::Maybe(maybe) => {
                let args = &maybe.args;
                let mut heap = HeapProduce {
                    scope_value: maybe.value,
                    new_scope: HashMap::new(),
                };
                let Resource::Named(named) = &maybe.resource else {
                    panic!("can only access attributes of named resources")
                };
                (named.typ.fun)(&mut heap, args).unwrap();

                let mut once = OncePart {
                    resource: maybe.resource.clone(),
                    args: args.to_owned(),
                    map: heap.new_scope,
                };
                once.cond_and(&maybe.cond);

                *self = NewPart::Partial(once);
                let NewPart::Partial(once) = self else {
                    unreachable!()
                };
                once
            }
            NewPart::Partial(once) => once,
            _ => {
                panic!()
            }
        }
    }

    pub fn cond_and(&mut self, cond: &Term) {
        match self {
            NewPart::Forall(forall) => {
                forall.mask = forall.mask.and(&FuncTerm::always(cond.clone()));
            }
            NewPart::Maybe(maybe) => {
                maybe.cond = maybe.cond.bool_and(cond);
            }
            NewPart::Partial(once) => {
                once.cond_and(cond);
            }
        }
    }
}

impl OncePart {
    pub fn cond_and(&mut self, cond: &Term) {
        self.map.values_mut().for_each(|v| v.cond_and(cond));
    }
}

pub(super) struct HeapConsume<'a> {
    pub inner: &'a mut SubContext,
    pub translate: HashMap<String, Translate>,
    pub old_scope: HashMap<String, NewPart>,
}

#[derive(Clone)]
pub enum Translate {
    Slice(Proj, Rc<dyn Fn(&[Term]) -> Vec<Term>>),
    JustOne(Proj),
    Select(Proj, Vec<Term>),
    Build(HashMap<String, Translate>, Vec<Term>),
}

pub type ForProj = Rc<dyn Fn(&mut NewPart) -> &mut ForPart>;

impl Translate {
    pub fn simple(name: String) -> Self {
        Self::JustOne(Proj {
            first: name,
            parts: vec![],
        })
    }
}

#[derive(Clone)]
pub struct Proj {
    pub first: String,
    pub parts: Vec<String>,
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
    pub new_scope: HashMap<String, NewPart>,
}

impl NewPart {
    pub fn get_byte(&self, idx: &[Term]) -> Term {
        let NewPart::Forall(forall) = self else {
            panic!();
        };
        assert!(forall.resource == Resource::Owned);
        forall.value.apply(idx)
    }
}

pub trait Heap {
    fn exactly(&mut self, name: &str, part: NewPart) -> Result<(), ConsumeErr>;
    fn forall(&mut self, name: &str, forall: Forall) -> Result<NewPart, ConsumeErr>;
    fn maybe(&mut self, name: &str, maybe: Maybe) -> Result<NewPart, ConsumeErr>;

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
    fn exactly(&mut self, name: &str, need: NewPart) -> Result<(), ConsumeErr> {
        match &need {
            NewPart::Forall(forall) => {
                let forall_arg = Forall {
                    resource: forall.resource.clone(),
                    mask: forall.mask.clone(),
                };
                let have = self.forall(name, forall_arg)?;
                self.assume.check_eq_part(&have, &need);
            }
            NewPart::Maybe(maybe) => {
                let switch = Maybe {
                    resource: maybe.resource.clone(),
                    args: maybe.args.clone(),
                    cond: maybe.cond,
                };
                let have = self.maybe(name, switch)?;
                self.assume.check_eq_part(&have, &need);
            }
            NewPart::Partial(_) => {
                panic!("i don't think this can happen")
                // might have to loop over the parts
            }
        }
        Ok(())
    }

    fn forall(&mut self, name: &str, need: Forall) -> Result<NewPart, ConsumeErr> {
        // TODO: optimization: skip everything if cond is impossible
        let trans = &self.translate[name];

        let Translate::JustOne(proj) = trans else {
            panic!("can not construct forall yet")
        };

        let have = self.lookup_resource(proj)?;
        // check that the resource type is correct
        assert!(&need.resource == have.resource());

        let part = if let Some(args) = have.args() {
            let idx = need.resource.make_fresh_args();
            let have_idx = FuncTerm::exactly(args).apply_bool(&idx);
            let need_idx = need.mask.apply_bool(&idx);
            let verify = need_idx.implies(&have_idx);
            assert!(self.assume.is_always_true(verify), "missing a resource");

            have.remove_maybe(&Maybe {
                resource: need.resource,
                args: args.to_owned(),
                cond: need.mask.apply(args),
            })
        } else {
            let NewPart::Forall(forall) = have else {
                unreachable!()
            };

            // check that we have all the indices
            let idx = need.resource.make_fresh_args();
            let have_idx = forall.mask.apply_bool(&idx);
            let need_idx = need.mask.apply_bool(&idx);
            let verify = need_idx.implies(&have_idx);
            assert!(self.assume.is_always_true(verify), "missing a resource");

            forall.mask = forall.mask.difference(&need.mask);
            NewPart::Forall(ForPart {
                resource: need.resource,
                mask: need.mask,
                value: forall.value,
            })
        };

        let existing = self.old_scope.insert(name.to_owned(), part.clone());
        assert!(existing.is_none());

        Ok(part)
    }

    fn maybe(&mut self, name: &str, switch: Maybe) -> Result<NewPart, ConsumeErr> {
        let trans = &self.translate[name];

        if let Translate::Build(map) = trans {
            let Resource::Named(named) = &switch.resource else {
                panic!("can only construct named resources")
            };

            let mut heap = HeapConsume {
                translate: map.clone(),
                inner: self,
                old_scope: HashMap::new(),
            };
            (named.typ.fun)(&mut heap, &switch.args)?;

            let part = NewPart::Partial(OncePart {
                resource: switch.resource,
                args: switch.args,
                map: heap.old_scope,
            });

            let existing = self.old_scope.insert(name.to_owned(), part.clone());
            assert!(existing.is_none());

            return Ok(part);
        }

        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
        };
        self.forall(name, forall)
    }
}

impl Heap for HeapProduce {
    fn exactly(&mut self, name: &str, part: NewPart) -> Result<(), ConsumeErr> {
        let existing = self.new_scope.insert(name.to_owned(), part);
        assert!(existing.is_none());
        Ok(())
    }

    fn forall(&mut self, name: &str, have: Forall) -> Result<NewPart, ConsumeErr> {
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
        let part = NewPart::Forall(ForPart {
            resource: have.resource,
            mask: have.mask,
            value,
        });

        let existing = self.new_scope.insert(name.to_owned(), part.clone());
        assert!(existing.is_none());
        Ok(part)
    }

    fn maybe(&mut self, name: &str, switch: Maybe) -> Result<NewPart, ConsumeErr> {
        // TODO: it would be nice if we did not have to specify indices when using these
        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
        };
        let res = self.forall(name, forall)?;
        Ok(res)
    }
}

impl NewPart {
    fn remove_maybe(&mut self, need: &Maybe) -> NewPart {
        match self {
            NewPart::Forall(have) => {
                let need_mask = FuncTerm::exactly(&need.args).and(&FuncTerm::always(need.cond));
                have.mask = have.mask.difference(&need_mask);
                NewPart::Maybe(MaybePart {
                    resource: need.resource,
                    args: need.args.clone(),
                    cond: need.cond,
                    value: have.value.apply(&need.args),
                })
            }
            NewPart::Maybe(have) => {
                have.cond = have.cond.bool_and(&need.cond.bool_not());
                NewPart::Maybe(MaybePart {
                    resource: need.resource,
                    args: need.args.clone(),
                    cond: need.cond,
                    value: have.value,
                })
            }
            NewPart::Partial(have) => {
                let heap = HeapConsume {
                    inner: todo!(),
                    translate: todo!(),
                    old_scope: todo!(),
                };
            }
        }
    }
}

impl SubContext {
    fn remove_resource(&mut self, trans: &Translate) -> Result<&mut NewPart, ConsumeErr> {
        match trans {
            Translate::Slice(_) => todo!(),
            Translate::JustOne(_) => todo!(),
            Translate::Select(_, _) => todo!(),
            Translate::Build(_, _) => todo!(),
        }

        let mut part = &mut self.forall[&proj.first];

        for name in &proj.parts {
            let NewPart::Partial(once) = part else {
                panic!()
            };
            part = &mut once.map[name];
        }

        Ok(part)
    }

    // let removed = &mut self.removed[&proj.first];

    //     fn conflict(proj: &[(Vec<Term>, String)], removed: &Removed) -> Term {
    //         let [(args1, name), proj @ ..] = proj else {
    //             todo!()
    //         };
    //         let mut total = removed.mask.apply(args1);
    //         for (args2, item, inner) in &removed.list {
    //             if item != name {
    //                 continue;
    //             }
    //             let mut cond = conflict(proj, inner);
    //             for (a, b) in zip_eq(args1, &args2[..]) {
    //                 cond = a.eq(b).bool_and(&cond);
    //             }
    //             total = total.bool_or(&cond);
    //         }
    //         total
    //     }

    //     let cond = conflict(&proj.parts, removed);
    //     assert!(self.assume.is_always_true(cond.to_bool().not()));

    fn remove_resource(&mut self, remove: Removed, res: &Resource) -> Result<(), ConsumeErr> {
        for rem in &self.removed {
            let Some(mut cond) = remove.proj.eq(&rem.proj) else {
                continue;
            };
            let len = min(remove.proj.parts.len(), rem.proj.parts.len());
            match (&remove.proj.parts[len..], &rem.proj.parts[len..]) {
                ([(args, _), ..], []) => {
                    cond = rem.mask.apply(args).bool_and(&cond);
                }
                ([], [(args, _), ..]) => {
                    cond = remove.mask.apply(args).bool_and(&cond);
                }
                ([], []) => {
                    let args = res.make_fresh_args();
                    cond = remove.mask.apply(&args).bool_and(&cond);
                    cond = rem.mask.apply(&args).bool_and(&cond);
                }
                _ => panic!(),
            }

            assert!(self.assume.is_always_true(cond.to_bool().not()));
        }

        self.removed.push(remove);
        Ok(())
    }
}

impl Proj {
    pub fn eq(&self, rhs: &Proj) -> Option<Term> {
        if self.first != rhs.first {
            return None;
        }

        let mut cond = Term::bool(true);
        let len = min(self.parts.len(), rhs.parts.len());
        for (a, b) in zip(&self.parts[..len], &rhs.parts[..len]) {
            if a.1 != b.1 {
                return None;
            }
            for (a, b) in zip_eq(&a.0, &b.0) {
                cond = a.eq(b).bool_and(&cond);
            }
        }
        Some(cond)
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
