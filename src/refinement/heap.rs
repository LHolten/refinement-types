use std::{
    fmt::Write,
    mem::take,
    rc::{Rc, Weak},
    sync::atomic::{AtomicUsize, Ordering},
};

use indenter::indented;
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;
use z3::{
    ast::{Bool, Dynamic},
    FuncDecl, Model, SatResult, Sort,
};

use crate::solver::ctx;

use super::{
    typing::zip_eq, Cond, Data, Forall, ForallTerm, Name, PosTyp, Resource, SubContext, Term,
    UnTerm,
};

#[derive(Clone)]
#[allow(clippy::type_complexity)]
pub enum FuncTerm {
    Free(Rc<FuncDecl<'static>>),
    User(Rc<dyn Fn(&[Term]) -> UnTerm>),
}

impl FuncTerm {
    pub fn new<F: Fn(&[Term]) -> UnTerm + 'static>(f: F) -> Self {
        Self::User(Rc::new(f))
    }

    pub fn new_bool<F: Fn(&[Term]) -> Bool<'static> + 'static>(f: F) -> Self {
        Self::new(move |x| UnTerm {
            inner: Dynamic::from_ast(&(f)(x)),
        })
    }

    pub fn apply_bool(&self, idx: &[Term]) -> Bool<'static> {
        self.apply(idx).inner.as_bool().unwrap()
    }

    pub fn apply(&self, idx: &[Term]) -> UnTerm {
        match self {
            FuncTerm::Free(f) => {
                let args: Vec<_> = idx.iter().map(|x| x.to_bv()).collect();
                let args: Vec<_> = args.iter().map(|x| x as _).collect();
                UnTerm {
                    inner: f.apply(&args),
                }
            }
            FuncTerm::User(func) => (func)(idx),
        }
    }

    pub fn difference(&self, other: &Self) -> Self {
        let this = self.clone();
        let other = other.clone();
        Self::new_bool(move |idx| this.apply_bool(idx) & !other.apply_bool(idx))
    }

    pub fn ite(&self, then: &Self, other: &Self) -> Self {
        let (cond, then, other) = (self.clone(), then.clone(), other.clone());
        Self::new(move |idx| {
            let (then, other) = (then.apply(idx), other.apply(idx));
            UnTerm {
                inner: cond.apply_bool(idx).ite(&then.inner, &other.inner),
            }
        })
    }

    pub fn exactly(ptr: &[Term]) -> Self {
        let ptr = ptr.to_owned();
        Self::new_bool(move |val| {
            zip_eq(&ptr, val)
                .map(|(l, r)| l.eq(r).to_bool())
                .fold(Bool::from_bool(ctx(), true), |l, r| l & r)
        })
    }

    pub fn and(&self, other: &Self) -> Self {
        let this = self.clone();
        let other = other.clone();
        Self::new_bool(move |idx| this.apply_bool(idx) & other.apply_bool(idx))
    }

    fn free(arg_size: &[(u32, String)]) -> Self {
        static ID: AtomicUsize = AtomicUsize::new(0);
        let name = format!("heap-{}", ID.fetch_add(1, Ordering::Relaxed));
        let domain: Vec<_> = arg_size
            .iter()
            .map(|(sz, _name)| Sort::bitvector(ctx(), *sz))
            .collect();
        let domain: Vec<_> = domain.iter().collect();
        let f = FuncDecl::new(ctx(), name, &domain, &Sort::bitvector(ctx(), 8));
        Self::Free(Rc::new(f))
    }
}

impl Resource {
    fn free_func(&self) -> FuncTerm {
        match self {
            Resource::Named(named) => {
                let named = named.upgrade().unwrap();
                let name = format!("name-{}", named.id);
                let arg_sizes = named.typ.tau.iter();
                let mut domain: Vec<_> = arg_sizes
                    .map(|(sz, _name)| Sort::bitvector(ctx(), *sz))
                    .collect();
                domain.push(Sort::uninterpreted(ctx(), "world".into()));
                let domain: Vec<_> = domain.iter().collect();
                let f = FuncDecl::new(ctx(), name, &domain, &Sort::bitvector(ctx(), 8));

                FuncTerm::Free(Rc::new(f))
            }
            Resource::Owned => todo!(),
        }
    }
}

pub trait Heap {
    // load bytes and store in size bits
    fn owned(&mut self, ptr: &Term, bytes: u32, size: u32) -> Result<Term, ConsumeErr> {
        let mut res = self.owned_byte(ptr, None)?;
        let mut ptr = ptr.clone();
        for _ in 1..bytes {
            ptr = ptr.add(&Term::nat(1, 32));
            // little endian, so new value is more significant
            let val = self.owned_byte(&ptr, None)?;
            res = val.concat(&res);
        }
        Ok(res.extend_to(size))
    }
    fn owned_byte(&mut self, ptr: &Term, span: Option<SourceSpan>) -> Result<Term, ConsumeErr> {
        let value = self.forall(Forall {
            named: Resource::Owned,
            mask: FuncTerm::exactly(&[ptr.to_owned()]),
            span,
        })?;
        Ok(value.apply(&[ptr.to_owned()]).byte())
    }
    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr>;
    fn forall(&mut self, forall: Forall) -> Result<FuncTerm, ConsumeErr>;
    fn forall_term(&mut self, term: ForallTerm) -> Result<(), ConsumeErr>;
    fn switch(&mut self, cond: Cond) -> Result<(), ConsumeErr> {
        let condition = FuncTerm::new_bool(move |_| cond.cond.to_bool());
        self.forall(Forall {
            named: Resource::Named(cond.named),
            mask: FuncTerm::exactly(&cond.args).and(&condition),
            span: Some(cond.span),
        })?;
        Ok(())
    }

    fn named(&mut self, name: Weak<Name>, args: &[Term]) -> Result<Data, ConsumeErr>;
    fn named_exact(
        &mut self,
        name: Weak<Name>,
        args: &[Term],
        data: Data,
    ) -> Result<(), ConsumeErr>;
}
pub(super) struct ConsumeFree<'a>(pub &'a mut SubContext, pub &'a mut Vec<Data>);

impl ConsumeFree<'_> {
    fn forall_inner(&mut self, need: Forall) -> Result<FuncTerm, ConsumeErr> {
        match self.try_remove(need) {
            Ok(res) => Ok(res),
            Err(need) => Err(ConsumeErr::MissingResource {
                resource: need.span,
                help: self.counter_example(need),
            }),
        }
    }
}

impl Heap for ConsumeFree<'_> {
    fn switch(&mut self, cond: Cond) -> Result<(), ConsumeErr> {
        let condition = FuncTerm::new_bool(move |_| cond.cond.to_bool());
        let need = Forall {
            named: Resource::Named(cond.named.clone()),
            mask: FuncTerm::exactly(&cond.args).and(&condition),
            span: Some(cond.span),
        };

        if let Err(need) = self.try_remove(need) {
            let res = need.mask.apply_bool(&cond.args);
            if self.is_always_true(res) {
                // TODO: add a wrapper to make this clearer
                (cond.named.upgrade().unwrap().typ.fun)(self, &cond.args, ())?;
            } else {
                return Err(ConsumeErr::MissingResource {
                    resource: need.span,
                    help: self.counter_example(need),
                });
            }
        }
        Ok(())
    }

    // This one stores the result
    fn forall(&mut self, need: Forall) -> Result<FuncTerm, ConsumeErr> {
        let res = self.forall_inner(need)?;
        self.1.push(Data::Func(res.clone()));
        Ok(res)
    }

    fn forall_term(&mut self, need: ForallTerm) -> Result<(), ConsumeErr> {
        let fresh = need.forall.make_fresh_args();
        let assume = need.forall.mask.apply_bool(&fresh);

        let have = self.forall_inner(need.forall)?;
        let cond = have.apply(&fresh).eq(&need.func.apply(&fresh));
        self.assume_verify_prop(&assume, &cond).unwrap();
        Ok(())
    }

    fn assert(&mut self, phi: Term, span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        if let Err(model) = self.verify_prop(&phi) {
            let mut out = String::new();
            format_model(indented(&mut out), model);
            return Err(ConsumeErr::InvalidAssert {
                assert: span,
                help: format!(
                    "Here is a valid example for which \n\
                    the assertion is false: \n{out}"
                ),
            });
        };
        Ok(())
    }

    fn named(&mut self, name: Weak<Name>, args: &[Term]) -> Result<Data, ConsumeErr> {
        let named = name.upgrade().unwrap();
        let mut new = vec![];
        let mut free = ConsumeFree(&mut self.0, &mut new);
        let PosTyp = (named.typ.fun)(&mut free, args, ())?;
        self.1.push(Data::Named(new.clone()));
        Ok(Data::Named(new))
    }

    fn named_exact(
        &mut self,
        name: Weak<Name>,
        args: &[Term],
        unterm: Data,
    ) -> Result<(), ConsumeErr> {
        let named = name.upgrade().unwrap();
        let mut new = vec![];
        let mut free = ConsumeFree(&mut self.0, &mut new);
        let PosTyp = (named.typ.fun)(&mut free, args, ())?;
        self.verify_equal(unterm, Data::Named(new));
        Ok(())
    }
}

impl SubContext {
    fn verify_equal(&self, left: Data, right: Data) {
        todo!()
    }
}

impl<'a> std::ops::DerefMut for ConsumeFree<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<'a> std::ops::Deref for ConsumeFree<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

pub(super) struct ProduceExact<'a>(pub &'a mut SubContext, pub &'a mut Data);

impl Heap for ProduceExact<'_> {
    // This one removes the result
    fn forall(&mut self, forall: Forall) -> Result<FuncTerm, ConsumeErr> {
        let value = self.1.as_func(forall.named);
        self.forall.push(ForallTerm {
            forall,
            func: value.clone(),
        });
        Ok(value)
    }

    fn forall_term(&mut self, term: ForallTerm) -> Result<(), ConsumeErr> {
        self.forall.push(term);
        Ok(())
    }

    fn assert(&mut self, phi: Term, _span: Option<SourceSpan>) -> Result<(), ConsumeErr> {
        self.assume.push(phi);
        Ok(())
    }

    fn named(&mut self, name: Weak<Name>, args: &[Term]) -> Result<Data, ConsumeErr> {
        let named = name.upgrade().unwrap();
        let mut new = self.1.as_named();
        let new_clone = new.clone();
        let mut free = ProduceExact(&mut self.0, &mut new);
        let PosTyp = (named.typ.fun)(&mut free, args, ())?;
        Ok(new_clone)
    }

    fn named_exact(
        &mut self,
        name: Weak<Name>,
        args: &[Term],
        mut new: Data,
    ) -> Result<(), ConsumeErr> {
        let named = name.upgrade().unwrap();
        let mut free = ProduceExact(&mut self.0, &mut new);
        let PosTyp = (named.typ.fun)(&mut free, args, ())?;
        Ok(())
    }
}

impl<'a> std::ops::DerefMut for ProduceExact<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0
    }
}

impl<'a> std::ops::Deref for ProduceExact<'a> {
    type Target = SubContext;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

struct Removal {
    mask: FuncTerm,
    value: FuncTerm,
}

fn build_value(mut removals: Vec<Removal>) -> FuncTerm {
    let mut out = removals.pop().unwrap().value;
    for removal in removals.iter() {
        out = removal.mask.ite(&removal.value, &out);
    }
    out
}

pub fn format_model<F: Write>(mut f: F, model: Model<'_>) {
    writeln!(f, "{model}").unwrap();
    // for x in &model {
    //     let name = x.name();
    //     let name = name.split('!').next().unwrap();
    //     assert_eq!(x.arity(), 0);
    //     let res = model.eval(&x.apply(&[]), false).unwrap();
    //     writeln!(f, "{name} = {}", res.as_bv().unwrap().as_u64().unwrap()).unwrap();
    // }
}

impl SubContext {
    fn counter_example(&mut self, need: Forall) -> String {
        let idx = need.make_fresh_args();
        let s = self.assume();
        s.assert(&need.mask.apply_bool(&idx));
        for ctx_forall in &self.forall {
            if ctx_forall.forall.id() == need.id() {
                s.assert(&ctx_forall.forall.mask.apply_bool(&idx).not());
            }
        }
        let SatResult::Sat = s.check() else { panic!() };
        let model = s.get_model().unwrap();
        let mut out = String::new();
        format_model(indented(&mut out), model);
        format!(
            "Here is a valid example for which \n\
            the resource does not exist: \n{out}"
        )
    }

    fn try_remove(&mut self, mut need: Forall) -> Result<FuncTerm, Forall> {
        let mut forall_list = take(&mut self.forall);
        let mut removals = vec![];

        // first we consume small allocations
        for alloc in forall_list.iter_mut() {
            if alloc.forall.id() != need.id() {
                continue;
            }
            let overlap = Forall {
                named: need.named.clone(),
                mask: alloc.forall.mask.and(&need.mask),
                span: None,
            };
            if !self.still_possible(&overlap) {
                continue;
            }
            let old_alloc_mask = alloc.forall.mask.clone();
            alloc.forall.mask = old_alloc_mask.difference(&need.mask);
            need.mask = need.mask.difference(&old_alloc_mask);
            removals.push(Removal {
                mask: old_alloc_mask,
                value: alloc.func.clone(),
            })
        }
        self.forall = forall_list;

        if self.still_possible(&need) {
            Err(need)
        } else {
            Ok(build_value(removals))
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
