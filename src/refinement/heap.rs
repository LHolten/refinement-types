use std::{cmp::min, collections::HashMap, iter::zip};

use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::ast::BV;

use crate::{refinement::typing::zip_eq, solver::ctx};

use super::{func_term::FuncTerm, term::Term, CtxForall, Forall, Resource, SubContext, Switch};

#[derive(Clone)]
pub struct ForPart {
    pub resource: Resource,
    pub mask: FuncTerm,
    pub value: FuncTerm,
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
    Once(OncePart),
}

impl NewPart {
    pub fn resource(&self) -> &Resource {
        match self {
            NewPart::Forall(forall) => &forall.resource,
            NewPart::Once(once) => &once.resource,
        }
    }

    pub fn mask(&self) -> FuncTerm {
        match self {
            NewPart::Forall(forall) => forall.mask.clone(),
            NewPart::Once(once) => FuncTerm::exactly(&once.args),
        }
    }

    pub fn is_instance(&self) -> bool {
        matches!(self, NewPart::Once(_))
    }

    // get an instance from a forall resource
    pub fn instance(&self, args: &[Term]) -> OncePart {
        let (part, cond) = match self {
            NewPart::Forall(forall) => {
                let mut heap = HeapProduce {
                    scope_value: forall.value.apply(args),
                    new_scope: HashMap::new(),
                };
                let Resource::Named(named) = &forall.resource else {
                    panic!("can only access attributes of named resources")
                };
                (named.typ.fun)(&mut heap, args).unwrap();

                let cond = forall.mask.apply(args);
                let part = OncePart {
                    resource: forall.resource,
                    args: args.to_owned(),
                    map: heap.new_scope,
                };
                (part, cond)
            }
            NewPart::Once(once) => {
                let mut cond = Term::bool(true);
                for (a, b) in zip_eq(&once.args, args) {
                    cond = a.eq(b).bool_and(&cond);
                }
                (once.clone(), cond)
            }
        };

        part.cond_and(&cond)
    }

    pub fn cond_and(self, cond: &Term) -> Self {
        match self {
            NewPart::Forall(forall) => NewPart::Forall(ForPart {
                mask: forall.mask.and(&FuncTerm::always(cond.clone())),
                ..forall
            }),
            NewPart::Once(once) => NewPart::Once(once.cond_and(cond)),
        }
    }
}

impl OncePart {
    pub fn cond_and(self, cond: &Term) -> Self {
        OncePart {
            map: self
                .map
                .into_iter()
                .map(|(k, v)| (k, v.cond_and(cond)))
                .collect(),
            ..self
        }
    }
}

#[derive(Clone)]
pub struct Removed {
    proj: Proj,
    mask: FuncTerm,
}

pub(super) struct HeapConsume<'a> {
    pub inner: &'a mut SubContext,
    pub translate: HashMap<String, Translate>,
    pub old_scope: HashMap<String, NewPart>,
}

#[derive(Clone)]
pub enum Translate {
    Just(Proj),
    Construct(HashMap<String, Translate>),
}

impl Translate {
    pub fn simple(name: String) -> Self {
        Self::Just(Proj {
            first: name,
            parts: vec![],
        })
    }
}

#[derive(Clone)]
pub struct Proj {
    first: String,
    parts: Vec<(Vec<Term>, String)>,
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

pub struct ForallRes {
    // result of the unpacked resource
    pub removals: Vec<CtxForall>,
}

impl ForallRes {
    pub fn get_byte(&self, idx: &[Term]) -> Term {
        let mut val = BV::from_i64(ctx(), 0, 8);
        for removal in &self.removals {
            if let Resource::Owned = removal.have.resource {
                let cond = removal.have.mask.apply_bool(idx);
                let new = removal.value.apply(idx).to_bv();
                val = cond.ite(&new, &val);
            }
        }
        Term::BV(val)
    }
}

pub trait Heap {
    fn exactly(&mut self, name: &str, part: NewPart) -> Result<(), ConsumeErr>;
    fn forall(&mut self, forall: Forall) -> Result<NewPart, ConsumeErr>;
    fn once(&mut self, switch: Switch) -> Result<NewPart, ConsumeErr>;

    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        let switch = Switch {
            resource: Resource::Impossible,
            args: vec![],
            cond: phi.bool_not(),
            name: "_".to_owned(),
            span,
        };

        self.once(switch)?;
        Ok(())
    }
}

impl Heap for HeapConsume<'_> {
    fn exactly(&mut self, name: &str, need: NewPart) -> Result<(), ConsumeErr> {
        match need {
            NewPart::Forall(forall) => {
                let forall_arg = Forall {
                    resource: forall.resource,
                    mask: forall.mask,
                    name: name.to_owned(),
                    span: None,
                };
                let have = self.forall(forall_arg)?;
                self.assume.check_eq_part(have, need);
            }
            NewPart::Once(once) => {
                let switch = Switch {
                    resource: once.resource,
                    args: once.args,
                    cond: Term::bool(true),
                    name: name.to_owned(),
                    span: None,
                };
                let have = self.once(switch)?;
                self.assume.check_eq_part(have, need);
            }
        }
        Ok(())
    }

    fn forall(&mut self, mut need: Forall) -> Result<NewPart, ConsumeErr> {
        // TODO: optimization: skip everything if cond is impossible
        let trans = &self.translate[&need.name];
        let Translate::Just(proj) = trans else {
            panic!("can not construct forall")
        };

        let have = self.lookup_resource(proj)?;
        // check that the resource type is correct
        assert!(&need.resource == have.resource());

        // check that we have all the indices
        let idx = need.resource.make_fresh_args();
        let cond = need
            .mask
            .apply_bool(&idx)
            .implies(&have.mask().apply_bool(&idx));
        assert!(self.assume.is_always_true(cond), "missing a resource");

        self.remove_resource(
            Removed {
                proj: proj.clone(),
                mask: need.mask,
            },
            &need.resource,
        )?;

        let part = match have {
            NewPart::Forall(have) => NewPart::Forall(ForPart {
                resource: have.resource,
                mask: need.mask,
                value: have.value,
            }),
            NewPart::Once(ref once) => have.cond_and(&need.mask.apply(&once.args)),
        };

        let existing = self.old_scope.insert(need.name.clone(), part);
        assert!(existing.is_none());

        Ok(part)
    }

    fn once(&mut self, switch: Switch) -> Result<NewPart, ConsumeErr> {
        let trans = &self.translate[&switch.name];

        if let Translate::Construct(map) = trans {
            let Resource::Named(named) = &switch.resource else {
                panic!("can only construct named resources")
            };

            let mut heap = HeapConsume {
                inner: self,
                translate: map.clone(),
                old_scope: HashMap::new(),
            };
            (named.typ.fun)(&mut heap, &switch.args)?;

            let part = NewPart::Once(OncePart {
                resource: switch.resource,
                args: switch.args,
                map: heap.old_scope,
            });

            let existing = self.old_scope.insert(switch.name.clone(), part);
            assert!(existing.is_none());

            return Ok(part);
        }

        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
            name: switch.name,
            span: switch.span,
        };
        self.forall(forall)
    }
}

impl Heap for HeapProduce {
    fn exactly(&mut self, name: &str, part: NewPart) -> Result<(), ConsumeErr> {
        let existing = self.new_scope.insert(name.to_owned(), part);
        assert!(existing.is_none());
        Ok(())
    }

    fn forall(&mut self, have: Forall) -> Result<NewPart, ConsumeErr> {
        let func = have.resource.associated_func();
        // we want to make sure that expanding the same resource twice gives the same result
        // this is why the values inside the forall are keyed by the parent value
        // TODO: optimization: this scope_value might not need to be "leveled" and could be replaced by the one at the root
        let value = FuncTerm::new(move |args| {
            let mut new_args = vec![self.scope_value.clone()];
            new_args.extend_from_slice(args);
            func.apply(&new_args)
        });
        let part = NewPart::Forall(ForPart {
            resource: have.resource,
            mask: have.mask,
            value,
        });

        let existing = self.new_scope.insert(have.name, part);
        assert!(existing.is_none());
        Ok(part)
    }

    fn once(&mut self, switch: Switch) -> Result<NewPart, ConsumeErr> {
        // TODO: it would be nice if we did not have to specify indices when using these
        let forall = Forall {
            resource: switch.resource,
            mask: FuncTerm::exactly(&switch.args).and(&FuncTerm::always(switch.cond)),
            name: switch.name,
            span: switch.span,
        };
        let res = self.forall(forall)?;
        Ok(res)
    }
}

impl SubContext {
    fn lookup_resource(&self, proj: &Proj) -> Result<NewPart, ConsumeErr> {
        let mut part = &self.forall[&proj.first];

        for (args, name) in &proj.parts {
            let once = part.instance(args);
            part = &once.map[name];
        }

        Ok(part.clone())
    }

    fn remove_resource(&mut self, remove: Removed, res: &Resource) -> Result<(), ConsumeErr> {
        'rem: for rem in &self.removed {
            if rem.proj.first != remove.proj.first {
                continue;
            }

            let mut cond = Term::bool(true);
            let len = min(remove.proj.parts.len(), rem.proj.parts.len());
            let (a, a_rem) = remove.proj.parts.split_at(len);
            let (b, b_rem) = rem.proj.parts.split_at(len);
            for (a, b) in zip(a, b) {
                if a.1 != b.1 {
                    continue 'rem;
                }
                for (a, b) in zip_eq(&a.0, &b.0) {
                    cond = a.eq(b).bool_and(&cond);
                }
            }
            match (a_rem, b_rem) {
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
