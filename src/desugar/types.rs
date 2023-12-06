use super::WeakNameList;
use crate::parse::expr::{Spanned, Value};
use crate::parse::types::{Constraint, NegTyp, PosTyp, Prop, Switch};
use crate::refinement;
use crate::refinement::heap::{ConsumeErr, Heap};
use crate::refinement::{func_term::FuncTerm, term::Term, typing::zip_eq, Resource};

use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone)]
pub struct DesugarTypes {
    pub(super) named: WeakNameList,
    pub terms: HashMap<String, Term>,
}

impl DesugarTypes {
    pub(super) fn new(list: WeakNameList) -> Self {
        Self {
            named: list,
            terms: HashMap::new(),
        }
    }

    pub fn convert_pos(&self, pos: Rc<Spanned<PosTyp>>) -> refinement::Fun<refinement::PosTyp> {
        let this = self.clone();
        let names = &pos.val.names;
        refinement::Fun {
            tau: names.iter().map(|name| (32, name.clone())).collect(),
            span: Some(pos.source_span()),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();
                this.terms
                    .extend(zip_eq(pos.val.names.clone(), terms.to_owned()));

                this.convert_constraint(&pos.val.parts, heap)?;

                Ok(refinement::PosTyp)
            }),
        }
    }

    pub fn convert_neg(&self, neg: NegTyp) -> refinement::Fun<refinement::NegTyp> {
        let NegTyp { args, ret } = neg;

        let this = self.clone();
        let names = &args.val.names;
        refinement::Fun {
            tau: names.iter().map(|name| (32, name.clone())).collect(),
            span: Some(args.source_span()),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();
                this.terms
                    .extend(zip_eq(args.val.names.clone(), terms.to_owned()));

                this.convert_constraint(&args.val.parts, heap)?;

                Ok(refinement::NegTyp {
                    arg: refinement::PosTyp,
                    ret: this.convert_pos(ret.clone()),
                })
            }),
        }
    }

    pub fn convert_prop(&self, prop: &Prop) -> Term {
        prop.convert(&self.terms).make_term()
    }

    pub fn convert_val(&self, val: &Value) -> Term {
        val.convert(&self.terms).make_term()
    }

    pub fn convert_vals(&self, vals: &[Value]) -> Vec<Term> {
        vals.iter().map(|x| self.convert_val(x)).collect()
    }

    pub fn convert_constraint(
        &mut self,
        parts: &[Spanned<Constraint>],
        heap: &mut dyn Heap,
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
                    heap.forall(refinement::Forall {
                        named,
                        span: Some(part.source_span()),
                        mask: FuncTerm::new_bool(move |terms| {
                            let mut this = this.clone();
                            this.terms.extend(zip_eq(names.clone(), terms.to_owned()));
                            this.convert_prop(&cond).to_bool()
                        }),
                    })?;
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
                        let args = [self.convert_val(ptr)];

                        let value = heap.forall(refinement::Forall {
                            named: Resource::Owned,
                            mask: FuncTerm::exactly(&args),
                            span: Some(part.source_span()),
                        })?;
                        let heap_val = value.apply(&args);

                        if let Some(new_name) = new_name.to_owned() {
                            self.terms.insert(new_name, heap_val.extend_to(32));
                        }
                    } else {
                        let named = self.named.0.get(name).unwrap().upgrade().unwrap();
                        (named.typ.fun)(heap, &self.convert_vals(&call.args.val))?;
                    }
                }
            }
        }
        Ok(())
    }
}
