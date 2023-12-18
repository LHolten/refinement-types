use crate::desugar::value::first;
use crate::parse::expr::{Spanned, Value};
use crate::parse::types::{Constraint, NegTyp, Param, ParamTyp, PosTyp, Prop};
use crate::refinement::heap::{ConsumeErr, Heap};
use crate::refinement::{func_term::FuncTerm, term::Term, typing::zip_eq, Resource};
use crate::{refinement, Nested};

use std::collections::HashMap;
use std::mem::replace;
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

    pub fn consume_args<T: Clone>(&self, args: &[T], pos: &[Param]) -> HashMap<String, Nested<T>> {
        let mut args = args.iter().cloned();
        let mut out = HashMap::new();
        for param in pos {
            let typ = self.val_typ(param);
            out.insert(param.name.clone(), typ.consume(&mut args));
        }
        assert!(args.next().is_none());
        out
    }

    pub fn convert_pos(&self, pos: Rc<Spanned<PosTyp>>) -> refinement::Fun<refinement::PosTyp> {
        let this = self.clone();
        refinement::Fun {
            tau: this.tau(&pos.val.names),
            span: Some(pos.source_span(self.offset)),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();
                this.terms.extend(this.consume_args(terms, &pos.val.names));

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
                this.terms.extend(this.consume_args(terms, &args.val.names));

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
    ) -> Result<Exactly, ConsumeErr> {
        fn accept() -> Exactly {
            Rc::new(|_: &mut dyn Heap| Ok(()))
        }

        let mut out = accept();
        let mut append = |func: Exactly| {
            let prev = replace(&mut out, accept());
            out = Rc::new(move |h: &mut dyn Heap| {
                prev(h)?;
                func(h)
            });
        };

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
                        named: self.get_resource(&forall.named),
                        span: Some(part.source_span(self.offset)),
                        mask: FuncTerm::new_bool(move |terms| {
                            let terms = terms.iter().cloned().map(Nested::Just);

                            let mut this = this.clone();
                            this.terms.extend(zip_eq(names.clone(), terms));
                            this.convert_prop(&cond).to_bool()
                        }),
                    };

                    let res = heap.forall(forall.clone(), None)?;
                    let equal = Rc::new(move |h: &mut dyn Heap| {
                        h.forall(forall.clone(), Some(res.clone()))?;
                        Ok(())
                    });
                    append(equal);
                }
                Constraint::Assert(cond) => {
                    heap.assert(self.convert_prop(cond), Some(part.source_span(self.offset)))?;
                    // TODO: does this need to be appended?
                }
                Constraint::Switch(new_name, switch) => {
                    let params = self.get_params(&switch.named);
                    let args = self.convert_vals(&switch.args, &params);

                    let cond_param = Param {
                        name: "@cond".to_owned(),
                        typ: ParamTyp::I32,
                    };
                    let cond = switch.cond.as_ref();
                    let cond = cond
                        .map(|v| first(self.convert_val(v, &cond_param)))
                        .unwrap_or(Term::bool(true));

                    let forall = refinement::Forall {
                        named: self.get_resource(&switch.named),
                        mask: FuncTerm::exactly(&args).and(&FuncTerm::new(move |_| cond.clone())),
                        span: Some(part.source_span(self.offset)),
                    };

                    let res = heap.forall(forall.clone(), None)?;
                    let res_val = res.apply(&args).extend_to(32);
                    let equal = Rc::new(move |h: &mut dyn Heap| {
                        h.forall(forall.clone(), Some(res.clone()))?;
                        Ok(())
                    });
                    append(equal.clone());

                    if let Some(new_name) = new_name.to_owned() {
                        assert!(switch.cond.is_none());
                        self.exactly.insert(new_name.clone(), equal);
                        self.terms.insert(new_name, Nested::Just(res_val));
                    }
                }
                Constraint::Inline(new_name, call) => {
                    let name = call.func.as_ref().unwrap();
                    let named = self.named.0.get(name).unwrap();
                    let args = self.convert_vals(&call.args.val, &named.typ.val.names);

                    let mut this = self.clone();
                    this.terms
                        .extend(this.consume_args(&args, &named.typ.val.names));

                    let equal = this.convert_constraint(&named.typ.val.parts, heap)?;
                    append(equal.clone());

                    if let Some(new_name) = new_name.clone() {
                        self.exactly.insert(new_name.clone(), equal);
                        self.terms
                            .insert(new_name, Nested::More(Some(named.id), this.terms));
                    }
                }
                Constraint::Exactly(name) => {
                    let equal = self.exactly.get(name).unwrap();
                    equal(heap)?;
                    append(equal.clone());
                }
            }
        }

        Ok(out)
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
