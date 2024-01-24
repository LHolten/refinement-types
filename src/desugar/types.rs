use crate::error::MultiFile;
use crate::parse::expr::{Spanned, Value};
use crate::parse::types::{Constraint, NegTyp, PosTyp, Prop};
use crate::refinement::heap::{ConsumeErr, Heap};
use crate::refinement::{func_term::FuncTerm, term::Term, typing::zip_eq, Resource};
use crate::{refinement, Nested};

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::value::IntoScope;

#[derive(Clone)]
pub struct Named {
    pub id: usize,
    pub typ: Rc<Spanned<PosTyp>>,
}

impl Named {
    pub fn new(typ: Rc<Spanned<PosTyp>>) -> Self {
        static NAME_ID: AtomicUsize = AtomicUsize::new(0);
        Self {
            id: NAME_ID.fetch_add(1, Ordering::Relaxed),
            typ,
        }
    }
}

#[derive(Clone, Default)]
pub struct NameList(pub HashMap<String, Named>);

#[derive(Clone)]
pub struct DesugarTypes {
    pub(super) named: NameList,
    pub terms: HashMap<String, Nested<Term>>,
    pub exactly: HashMap<String, Exactly>,
    pub source: MultiFile,
}

type Exactly = Rc<dyn Fn(&mut dyn Heap) -> Result<(), ConsumeErr>>;

impl DesugarTypes {
    pub(super) fn new(list: NameList, source: MultiFile) -> Self {
        Self {
            named: list,
            terms: HashMap::new(),
            exactly: HashMap::new(),
            source,
        }
    }

    pub fn tau(&self, names: &[String]) -> Vec<(u32, String)> {
        names.iter().map(|name| (32, name.clone())).collect()
    }

    pub fn consume_args<T: Clone>(&self, args: &[T], names: &[String]) -> Vec<(String, Nested<T>)> {
        zip_eq(names, args)
            .map(|(name, arg)| (name.clone(), Nested::Just(arg.clone())))
            .collect()
    }

    pub fn consume_terms(&mut self, terms: &[Term], names: &[String]) -> Result<(), ConsumeErr> {
        self.terms.extend(self.consume_args(terms, names));

        Ok(())
    }

    pub fn convert_pos(&self, pos: Rc<Spanned<PosTyp>>) -> refinement::Fun<refinement::PosTyp> {
        let this = self.clone();
        refinement::Fun {
            tau: this.tau(&pos.val.names),
            span: Some(pos.span),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();

                this.consume_terms(terms, &pos.val.names)?;
                this.convert_constraint(&pos.val.parts, heap)?;

                Ok(refinement::PosTyp)
            }),
        }
    }

    pub fn convert_neg(&self, neg: NegTyp) -> refinement::Fun<refinement::NegTyp> {
        let NegTyp { args, ret } = neg;

        let this = self.clone();
        refinement::Fun {
            tau: this.tau(&args.val.names),
            span: Some(args.span),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();

                this.consume_terms(terms, &args.val.names)?;
                this.convert_constraint(&args.val.parts, heap)?;

                Ok(refinement::NegTyp {
                    arg: refinement::PosTyp,
                    ret: this.convert_pos(ret.clone()),
                })
            }),
        }
    }

    pub fn convert_prop(&self, prop: &Prop) -> Term {
        self.source.unwrap(prop.convert(&self.terms)).make_term()
    }

    pub fn convert_val(&self, val: &Value) -> Term {
        self.source.unwrap(val.convert(&self.terms)).make_term()
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
                Constraint::Let(new_name, val) => {
                    let value = self.convert_val(val);
                    self.terms.insert(new_name.clone(), Nested::Just(value));
                }
                Constraint::Forall(forall) => {
                    let cond = forall.cond.clone();
                    let names = forall.names.clone();

                    let this = self.clone();
                    let forall = refinement::Forall {
                        resource: self.get_resource(&forall.named),
                        span: Some(part.span),
                        name: "_".to_owned(),
                        mask: FuncTerm::new_bool(move |terms| {
                            let terms = terms.iter().cloned().map(Nested::Just);

                            let mut this = this.clone();
                            this.terms.extend(zip_eq(names.clone(), terms));
                            this.convert_prop(&cond).to_bool()
                        }),
                    };

                    heap.forall(forall)?;
                }
                Constraint::Assert(cond) => {
                    heap.assert(self.convert_prop(cond), Some(part.span))?;
                }
                Constraint::Switch(new_name, switch) => {
                    let args = self.convert_vals(&switch.args);
                    let cond = switch.cond.as_ref();
                    let resource = self.get_resource(&switch.named);

                    let switch = refinement::Switch {
                        resource,
                        args,
                        span: Some(part.span),
                        name: "_".to_owned(),
                        cond: cond
                            .map(|v| self.convert_val(v))
                            .unwrap_or(Term::bool(true)),
                    };

                    let switch_clone = switch.clone();
                    heap.once(switch_clone)?;

                    if let Some(new_name) = new_name.to_owned() {
                        assert!(cond.is_none());
                        if let Resource::Owned = switch.resource {
                            let res_extended = res.get_byte(&switch.args).extend_to(32);
                            self.terms
                                .insert(new_name.clone(), Nested::Just(res_extended));
                        }

                        // let equal = Rc::new(move |h: &mut dyn Heap| {
                        //     for got in res.removals.clone() {
                        //         h.exactly(got)?;
                        //     }
                        //     Ok(())
                        // });
                        // self.exactly.insert(new_name, equal);
                    }
                }
                Constraint::Exactly(name) => {
                    let equal = self.source.unwrap(self.exactly.try_get(name));
                    equal(heap)?;
                }
            }
        }

        Ok(())
    }

    pub fn convert_named(&self, named: &Named) -> refinement::Name {
        refinement::Name {
            id: named.id,
            typ: self.convert_pos(named.typ.clone()),
        }
    }

    pub fn get_resource(&self, name: &Spanned<String>) -> Resource {
        match &*name.val {
            "@byte" => Resource::Owned,
            _ => {
                let named = self.source.unwrap(self.named.0.try_get(name));
                Resource::Named(self.convert_named(named))
            }
        }
    }
}
