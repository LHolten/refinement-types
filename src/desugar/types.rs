use crate::desugar::value::first;
use crate::parse::expr::{Spanned, Value};
use crate::parse::types::{Constraint, NegTyp, Param, ParamTyp, PosTyp, Prop};
use crate::refinement::heap::{ConsumeErr, Heap};
use crate::refinement::{func_term::FuncTerm, term::Term, typing::zip_eq, Resource};
use crate::{refinement, Nested};

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use super::value::ValTyp;

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
    pub offset: usize,
}

type Exactly = Rc<dyn Fn(&mut dyn Heap) -> Result<(), ConsumeErr>>;

impl DesugarTypes {
    pub(super) fn new(list: NameList, offset: usize) -> Self {
        Self {
            named: list,
            terms: HashMap::new(),
            exactly: HashMap::new(),
            offset,
        }
    }

    pub fn tau(&self, pos: &[Param]) -> Vec<(u32, String)> {
        let mut out = vec![];
        for param in pos {
            match &param.typ {
                ParamTyp::I32 => out.push((32, param.name.clone())),
                ParamTyp::Custom { name } => out.extend(
                    self.get_resource(name)
                        .arg_sizes()
                        .into_iter()
                        .map(|(size, name)| (size, format!("{}.{name}", &param.name))),
                ),
            }
        }
        out
    }

    pub fn consume_args<T: Clone>(&self, args: &[T], params: &[Param]) -> Vec<(String, Nested<T>)> {
        let mut args = args.iter().cloned();
        let mut out = Vec::new();
        for param in params {
            let typ = self.val_typ(param);
            out.push((param.name.clone(), typ.consume(&mut args)));
        }
        assert!(args.next().is_none());
        out
    }

    pub fn consume_terms(
        &mut self,
        terms: &[Term],
        params: &[Param],
        heap: &mut dyn Heap,
    ) -> Result<(), ConsumeErr> {
        let args = self.consume_args(terms, params);

        for ((_name, arg), param) in zip_eq(&args, params) {
            let typ = self.val_typ(param);
            match &param.typ {
                ParamTyp::I32 => {}
                ParamTyp::Custom { name } => {
                    let once = refinement::Switch {
                        args: arg
                            .collect(&typ)
                            .into_iter()
                            .map(|x| x.make_term())
                            .collect(),
                        resource: self.get_resource(name),
                        cond: Term::bool(true),
                        span: None,
                    };
                    let once_clone = once.clone();
                    let res = heap.apply(Box::new(|heap| heap.once(once_clone)))?;

                    let equal = Rc::new(move |h: &mut dyn Heap| {
                        for got in res.removals.clone() {
                            h.exactly(got)?;
                        }
                        Ok(())
                    });

                    self.exactly.insert(param.name.clone(), equal);
                }
            }
        }

        self.terms.extend(args);

        Ok(())
    }

    pub fn convert_pos(&self, pos: Rc<Spanned<PosTyp>>) -> refinement::Fun<refinement::PosTyp> {
        let this = self.clone();
        refinement::Fun {
            tau: this.tau(&pos.val.names),
            span: Some(pos.source_span(self.offset)),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();

                this.consume_terms(terms, &pos.val.names, heap)?;
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
            span: Some(args.source_span(self.offset)),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();

                this.consume_terms(terms, &args.val.names, heap)?;
                this.convert_constraint(&args.val.parts, heap)?;

                Ok(refinement::NegTyp {
                    arg: refinement::PosTyp,
                    ret: this.convert_pos(ret.clone()),
                })
            }),
        }
    }

    pub fn convert_prop(&self, prop: &Prop) -> Term {
        prop.convert(&self.terms, ValTyp::I32).make_term()
    }

    pub fn convert_val(&self, val: &Value, param: &Param) -> Vec<Term> {
        let typ = self.val_typ(param);
        val.convert(&self.terms, typ)
            .into_iter()
            .map(|x| x.make_term())
            .collect()
    }

    pub fn convert_vals(&self, vals: &[Value], params: &[Param]) -> Vec<Term> {
        zip_eq(vals, params)
            .flat_map(|(x, p)| self.convert_val(x, p))
            .collect()
    }

    pub fn convert_constraint(
        &mut self,
        parts: &[Spanned<Constraint>],
        heap: &mut dyn Heap,
    ) -> Result<(), ConsumeErr> {
        for part in parts {
            match &part.val {
                Constraint::Let(new_name, val) => {
                    let param = Param {
                        name: new_name.clone(),
                        typ: ParamTyp::I32,
                    };
                    let value = first(self.convert_val(val, &param));
                    self.terms.insert(new_name.clone(), Nested::Just(value));
                }
                Constraint::Forall(forall) => {
                    let cond = forall.cond.clone();
                    let names = forall.names.clone();

                    let this = self.clone();
                    let forall = refinement::Forall {
                        resource: self.get_resource(&forall.named),
                        span: Some(part.source_span(self.offset)),
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
                    heap.assert(self.convert_prop(cond), Some(part.source_span(self.offset)))?;
                }
                Constraint::Switch(new_name, switch) => {
                    let params = self.get_params(&switch.named);
                    let args = self.convert_vals(&switch.args, &params);

                    let cond_param = Param {
                        name: "@cond".to_owned(),
                        typ: ParamTyp::I32,
                    };
                    let cond = switch.cond.as_ref();

                    let resource = self.get_resource(&switch.named);

                    let switch = refinement::Switch {
                        resource,
                        args,
                        span: Some(part.source_span(self.offset)),
                        cond: cond
                            .map(|v| first(self.convert_val(v, &cond_param)))
                            .unwrap_or(Term::bool(true)),
                    };

                    let switch_clone = switch.clone();
                    let res = heap.apply(Box::new(move |heap| heap.once(switch_clone)))?;

                    if let Some(new_name) = new_name.to_owned() {
                        assert!(cond.is_none());
                        if let Resource::Owned = switch.resource {
                            let res_extended = res.get_byte(&switch.args).extend_to(32);
                            self.terms
                                .insert(new_name.clone(), Nested::Just(res_extended));
                        }

                        let equal = Rc::new(move |h: &mut dyn Heap| {
                            for got in res.removals.clone() {
                                h.exactly(got)?;
                            }
                            Ok(())
                        });
                        self.exactly.insert(new_name, equal);
                    }
                }
                Constraint::Exactly(name) => {
                    let equal = self.exactly.get(name).unwrap();
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

    pub fn get_resource(&self, name: &str) -> Resource {
        match name {
            "@byte" => Resource::Owned,
            _ => {
                let named = self.named.0.get(name).unwrap();
                Resource::Named(self.convert_named(named))
            }
        }
    }

    fn get_params(&self, name: &str) -> Vec<Param> {
        match name {
            "@byte" => vec![Param {
                name: "ptr".to_owned(),
                typ: ParamTyp::I32,
            }],
            _ => {
                let named = self.named.0.get(name).unwrap();
                named.typ.val.names.to_owned()
            }
        }
    }

    fn get_id(&self, name: &str) -> Option<usize> {
        match name {
            "@byte" => None,
            _ => {
                let named = self.named.0.get(name).unwrap();
                Some(named.id)
            }
        }
    }

    pub fn val_typ(&self, param: &Param) -> ValTyp {
        match &param.typ {
            ParamTyp::I32 => ValTyp::I32,
            ParamTyp::Custom { name } => ValTyp::Named {
                id: self.get_id(name),
                args: self
                    .get_params(name)
                    .into_iter()
                    .map(|param| (param.name.to_owned(), self.val_typ(&param)))
                    .collect(),
            },
        }
    }
}
