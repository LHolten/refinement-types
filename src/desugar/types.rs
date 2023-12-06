use crate::parse::expr::{Spanned, Value};
use crate::parse::types::{Constraint, NegTyp, PosTyp, Prop};
use crate::refinement;
use crate::refinement::heap::{ConsumeErr, Heap};
use crate::refinement::{func_term::FuncTerm, term::Term, typing::zip_eq, Resource};

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

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
    pub terms: HashMap<String, Term>,
    pub exactly: HashMap<String, NameExact>,
}

#[derive(Clone)]
pub struct NameExact {
    named: Named,
    args: Vec<Term>,
    res: Vec<Exactly>,
}

#[derive(Clone)]
pub enum Exactly {
    Named(Vec<Exactly>),
    Forall(FuncTerm),
}

impl Exactly {
    fn unwrap_named(self) -> Vec<Self> {
        match self {
            Exactly::Named(res) => res,
            _ => panic!(),
        }
    }

    fn unwrap_forall(self) -> FuncTerm {
        match self {
            Exactly::Forall(res) => res,
            _ => panic!(),
        }
    }
}

impl DesugarTypes {
    pub(super) fn new(list: NameList) -> Self {
        Self {
            named: list,
            terms: HashMap::new(),
            exactly: HashMap::new(),
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

                this.convert_constraint(&pos.val.parts, heap, None)?;

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

                this.convert_constraint(&args.val.parts, heap, None)?;

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
        mut exactly: Option<Vec<Exactly>>,
    ) -> Result<Vec<Exactly>, ConsumeErr> {
        let mut out = vec![];

        for part in parts {
            match &part.val {
                Constraint::Forall(forall) => {
                    let named = if forall.named == "@byte" {
                        Resource::Owned
                    } else {
                        let named = self.named.0.get(&forall.named).unwrap();
                        Resource::Named(self.convert_named(named))
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

                    let equal = exactly
                        .as_mut()
                        .map(|x| x.pop().unwrap())
                        .map(Exactly::unwrap_forall);
                    let res = heap.forall(forall, equal)?;
                    out.push(Exactly::Forall(res));
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

                        let forall = refinement::Forall {
                            named: Resource::Owned,
                            mask: FuncTerm::exactly(&args),
                            span: Some(part.source_span()),
                        };
                        let equal = exactly
                            .as_mut()
                            .map(|x| x.pop().unwrap())
                            .map(Exactly::unwrap_forall);
                        let value = heap.forall(forall, equal)?;
                        out.push(Exactly::Forall(value.clone()));

                        if let Some(new_name) = new_name.to_owned() {
                            let heap_val = value.apply(&args);
                            self.terms.insert(new_name, heap_val.extend_to(32));
                        }
                    } else {
                        let named = self.named.0.get(name).unwrap();
                        let args = self.convert_vals(&call.args.val);

                        let mut this = self.clone();
                        this.terms
                            .extend(zip_eq(named.typ.val.names.clone(), args.clone()));

                        let equal = exactly
                            .as_mut()
                            .map(|x| x.pop().unwrap())
                            .map(Exactly::unwrap_named);
                        let res = this.convert_constraint(&named.typ.val.parts, heap, equal)?;
                        out.push(Exactly::Named(res.clone()));

                        if let Some(new_name) = new_name.to_owned() {
                            let name_exact = NameExact {
                                named: named.clone(),
                                args,
                                res,
                            };
                            self.exactly.insert(new_name, name_exact);
                        }
                    }
                }
                Constraint::Exactly(name) => {
                    let name_exact = self.exactly.get(name).unwrap();

                    let mut this = self.clone();
                    this.terms.extend(zip_eq(
                        name_exact.named.typ.val.names.clone(),
                        name_exact.args.clone(),
                    ));

                    this.convert_constraint(
                        &name_exact.named.typ.val.parts,
                        heap,
                        Some(name_exact.res.clone()),
                    )?;
                }
            }
        }
        if let Some(eq) = exactly {
            assert!(eq.is_empty())
        }

        out.reverse();
        Ok(out)
    }

    pub fn convert_named(&self, named: &Named) -> refinement::Name {
        refinement::Name {
            id: named.id,
            typ: self.convert_pos(named.typ.clone()),
        }
    }
}
