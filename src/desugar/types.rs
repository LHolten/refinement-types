use crate::parse::expr::{Spanned, Value};
use crate::parse::types::{Constraint, NegTyp, PosTyp, Prop};
use crate::refinement::heap::{ConsumeErr, Heap};
use crate::refinement::{func_term::FuncTerm, term::Term, typing::zip_eq, Resource};
use crate::{refinement, Nested};

use std::collections::HashMap;
use std::mem::replace;
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
    pub terms: HashMap<String, Nested<Term>>,
    pub exactly: HashMap<String, Exactly>,
    pub offset: usize,
}

type Exactly = Rc<dyn Fn(&mut dyn Heap) -> Result<(), ConsumeErr>>;

// #[derive(Clone)]
// pub struct NameExact {
//     typ: Rc<Spanned<PosTyp>>,
//     args: Vec<Term>,
//     res: Nested<Term>,
// }

impl DesugarTypes {
    pub(super) fn new(list: NameList, offset: usize) -> Self {
        Self {
            named: list,
            terms: HashMap::new(),
            exactly: HashMap::new(),
            offset,
        }
    }

    pub fn convert_pos(&self, pos: Rc<Spanned<PosTyp>>) -> refinement::Fun<refinement::PosTyp> {
        let this = self.clone();
        let names = &pos.val.names;
        refinement::Fun {
            tau: names.iter().map(|name| (32, name.clone())).collect(),
            span: Some(pos.source_span(self.offset)),
            fun: Rc::new(move |heap, terms| {
                let terms = terms.iter().cloned().map(Nested::Just);
                let mut this = this.clone();
                this.terms.extend(zip_eq(pos.val.names.clone(), terms));

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
            span: Some(args.source_span(self.offset)),
            fun: Rc::new(move |heap, terms| {
                let terms = terms.iter().cloned().map(Nested::Just);
                let mut this = this.clone();
                this.terms.extend(zip_eq(args.val.names.clone(), terms));

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
                    let value = self.convert_val(val);
                    self.terms.insert(new_name.clone(), Nested::Just(value));
                }
                Constraint::Forall(forall) => {
                    let named = self.get_resource(&forall.named);

                    let cond = forall.cond.clone();
                    let names = forall.names.clone();

                    let this = self.clone();
                    let forall = refinement::Forall {
                        named,
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
                    let named = self.get_resource(&switch.named);
                    let args = self.convert_vals(&switch.args);

                    let cond = switch.cond.as_ref();
                    let cond = cond
                        .map(|v| self.convert_val(v))
                        .unwrap_or(Term::bool(true));

                    let forall = refinement::Forall {
                        named,
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
                    let args = self.convert_vals(&call.args.val);

                    let mut this = self.clone();
                    let args_iter = args.clone().into_iter().map(Nested::Just);
                    this.terms
                        .extend(zip_eq(named.typ.val.names.clone(), args_iter));

                    let equal = this.convert_constraint(&named.typ.val.parts, heap)?;
                    append(equal.clone());

                    if let Some(new_name) = new_name.clone() {
                        self.exactly.insert(new_name.clone(), equal);
                        self.terms.insert(new_name, Nested::More(this.terms));
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

    fn get_resource(&mut self, name: &str) -> Resource {
        match name {
            "@byte" => Resource::Owned,
            _ => {
                let named = self.named.0.get(name).unwrap();
                Resource::Named(self.convert_named(named))
            }
        }
    }
}
