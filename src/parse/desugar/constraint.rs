use super::Instance;
use super::{super::expr::Spanned, DesugarTypes};
use crate::parse::types::Switch;
use crate::refinement::heap::FuncTerm;
use crate::refinement::{self, ForallTerm, Resource};
use crate::refinement::{heap::ConsumeErr, typing::zip_eq};
use crate::{parse::types::Constraint, refinement::heap::Heap};
use std::rc::Rc;

impl DesugarTypes {
    pub fn convert_constraint(
        &mut self,
        parts: &[Spanned<Constraint>],
        heap: &mut dyn Heap,
        data: &mut dyn Dir,
    ) -> Result<(), ConsumeErr> {
        for part in parts {
            match &part.val {
                Constraint::Forall(forall) => {
                    let named = if forall.named == "@byte" {
                        Resource::Owned
                    } else {
                        Resource::Named(self.named.0.get(&forall.named).unwrap().clone())
                    };
                    let cond = forall.cond.clone();
                    let names = forall.names.clone();

                    let this = self.clone();
                    let forall = refinement::Forall {
                        named,
                        span: Some(part.source_span()),
                        mask: FuncTerm::new_bool(move |terms| {
                            let mut this = this.clone();
                            this.terms.extend(zip_eq(names.clone(), terms.to_owned()));
                            this.convert_prop(&cond).to_bool()
                        }),
                    };

                    data.forall(heap, forall)?;
                }
                Constraint::Switch(Switch { cond, named, args }) => {
                    let named = self.named.0.get(named).unwrap();

                    heap.switch(refinement::Cond {
                        named: named.clone(),
                        span: part.source_span(),
                        cond: self.convert_prop(cond),
                        args: self.convert_vals(args),
                    })?;
                }
                Constraint::Assert(cond) => {
                    heap.assert(self.convert_prop(cond), Some(part.source_span()))?;
                }
                Constraint::Builtin(new_name, call) => {
                    let name = call.func.as_ref().unwrap();
                    if name.starts_with('@') {
                        assert_eq!(name, "@byte");
                        let [ptr] = &*call.args.val else { panic!() };
                        let heap_val =
                            heap.owned_byte(&self.convert_val(ptr), Some(part.source_span()))?;
                        if let Some(new_name) = new_name.to_owned() {
                            self.terms.insert(new_name, heap_val.extend_to(32));
                        }
                    } else {
                        let named = self.named.0.get(name).unwrap().upgrade().unwrap();
                        let args = self.convert_vals(&call.args.val);

                        let exact = data.named(&named, heap, &args)?;

                        if let Some(new_name) = new_name.to_owned() {
                            self.for_terms.insert(
                                new_name,
                                Instance {
                                    func: Rc::new(move |heap| {
                                        let mut exact = exact.clone();
                                        (named.func)(heap, &mut exact, &args)?;
                                        Ok(refinement::PosTyp)
                                    }),
                                },
                            );
                        }
                    }
                }
                Constraint::BuiltinEq(name) => {
                    let inst = self.for_terms.get(name).unwrap();
                    (inst.func)(heap)?;
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
pub enum Data {
    Func(FuncTerm),
    Name(Vec<Data>),
}

#[derive(Clone, Default)]
pub struct Free {
    data: Vec<Data>,
}

#[derive(Clone, Default)]
pub struct Exact {
    data: Vec<Data>,
}

pub trait Dir {
    fn named(
        &mut self,
        named: &Rc<refinement::Name>,
        heap: &mut dyn Heap,
        args: &[refinement::Term],
    ) -> Result<Exact, ConsumeErr>;

    fn forall(&mut self, heap: &mut dyn Heap, forall: refinement::Forall)
        -> Result<(), ConsumeErr>;
}

impl Dir for Free {
    fn named(
        &mut self,
        named: &Rc<refinement::Name>,
        heap: &mut dyn Heap,
        args: &[refinement::Term],
    ) -> Result<Exact, ConsumeErr> {
        let mut free = Free::default();
        (named.func)(heap, &mut free, args)?;
        self.data.push(Data::Name(free.data.clone()));
        Ok(Exact { data: free.data })
    }

    fn forall(
        &mut self,
        heap: &mut dyn Heap,
        forall: refinement::Forall,
    ) -> Result<(), ConsumeErr> {
        let func = heap.forall(forall.clone())?;
        self.data.push(Data::Func(func));
        Ok(())
    }
}

impl Dir for Exact {
    fn named(
        &mut self,
        named: &Rc<refinement::Name>,
        heap: &mut dyn Heap,
        args: &[refinement::Term],
    ) -> Result<Exact, ConsumeErr> {
        let Data::Name(data) = self.data.remove(0) else {
            panic!()
        };
        let mut exact = Exact { data: data.clone() };
        (named.func)(heap, &mut exact, args)?;
        Ok(Exact { data })
    }

    fn forall(
        &mut self,
        heap: &mut dyn Heap,
        forall: refinement::Forall,
    ) -> Result<(), ConsumeErr> {
        let Data::Func(func) = self.data.remove(0) else {
            panic!()
        };
        heap.forall_term(ForallTerm { forall, func })?;
        Ok(())
    }
}
