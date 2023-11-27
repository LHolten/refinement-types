use std::{
    collections::HashMap,
    marker::PhantomData,
    rc::{Rc, UniqueRc, Weak},
};

use crate::{
    parse::expr::{IfZero, Let, Stmt},
    refinement::{
        self,
        heap::{FuncTerm, Heap},
        typing::zip_eq,
        Lambda, Resource, Val,
    },
    uninit_rc::UninitRc,
};

use super::{
    expr::{BinOpValue, Block, Def, FuncDef, Module, Value},
    types::{Constraint, NamedConstraint, NegTyp, PosTyp, Prop, PropOp, Switch},
};

type LazyName = Box<dyn Fn(WeakNameList) -> refinement::Name>;

#[derive(Default)]
struct LazyNameList(HashMap<String, (UniqueRc<refinement::Name>, LazyName)>);

#[derive(Clone)]
struct WeakNameList(HashMap<String, Weak<refinement::Name>>);

impl LazyNameList {
    pub fn weak(&self) -> WeakNameList {
        let iter = self.0.iter();
        let iter = iter.map(|(k, v)| (k.clone(), UniqueRc::downgrade(&v.0)));
        WeakNameList(iter.collect())
    }

    pub fn fix(mut self) -> Vec<Rc<refinement::Name>> {
        let list = self.weak();

        self.0.values_mut().for_each(|v| *v.0 = (v.1)(list.clone()));
        self.0
            .into_values()
            .map(|v| UniqueRc::into_rc(v.0))
            .collect()
    }
}

impl Value {
    pub fn convert<T: Clone>(&self, lookup: &HashMap<String, T>) -> refinement::Free<T> {
        match self {
            Value::Var(name) => refinement::Free::Var(
                lookup
                    .get(name)
                    .ok_or_else(|| {
                        format!(
                            "can not find `{name}`, have: {:?}",
                            lookup.keys().collect::<Vec<_>>()
                        )
                    })
                    .unwrap()
                    .clone(),
            ),
            Value::Int32(val) => refinement::Free::Just(*val as i64, 32),
            Value::BinOp(binop) => binop.convert(lookup),
            Value::Prop(prop) => prop.convert(lookup),
        }
    }
}

impl BinOpValue {
    pub fn convert<T: Clone>(&self, lookup: &HashMap<String, T>) -> refinement::Free<T> {
        let op = match self.op {
            super::expr::BinOp::Plus => refinement::BinOp::Add,
            super::expr::BinOp::Minus => refinement::BinOp::Sub,
            super::expr::BinOp::Times => refinement::BinOp::Mul,
            super::expr::BinOp::Modulo => refinement::BinOp::Rem,
        };
        refinement::Free::BinOp {
            l: Rc::new(self.l.convert(lookup)),
            r: Rc::new(self.r.convert(lookup)),
            op,
        }
    }
}

impl refinement::BinOp {
    pub fn free<T>(self, l: refinement::Free<T>, r: refinement::Free<T>) -> refinement::Free<T> {
        refinement::Free::BinOp {
            l: Rc::new(l),
            r: Rc::new(r),
            op: self,
        }
    }
}

impl Prop {
    pub fn convert<T: Clone>(&self, lookup: &HashMap<String, T>) -> refinement::Free<T> {
        let l = self.l.convert(lookup);
        let r = self.r.convert(lookup);
        use refinement::BinOp as Op;
        match self.op {
            PropOp::Less => Op::Less.free(l, r),
            PropOp::LessEq => Op::LessEq.free(l, r),
            PropOp::Eq => Op::Eq.free(l, r),
            PropOp::NotEq => Op::NotEq.free(l, r),
            PropOp::And => Op::And.free(l, r),
        }
    }
}

#[derive(Clone)]
pub struct DesugarTypes {
    named: WeakNameList,
    pub terms: HashMap<String, refinement::Term>,
}

impl DesugarTypes {
    pub fn convert_pos(&self, pos: Rc<PosTyp>) -> refinement::Fun<refinement::PosTyp> {
        let this = self.clone();
        refinement::Fun {
            tau: pos.names.iter().map(|_| 32).collect(),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();
                this.terms
                    .extend(zip_eq(pos.names.clone(), terms.to_owned()));

                this.convert_constraint(&pos.parts, heap);

                refinement::PosTyp
            }),
        }
    }

    pub fn convert_neg(&self, neg: NegTyp) -> refinement::Fun<refinement::NegTyp> {
        let NegTyp { args, ret } = neg;

        let this = self.clone();
        refinement::Fun {
            tau: args.names.iter().map(|_| 32).collect(),
            fun: Rc::new(move |heap, terms| {
                let mut this = this.clone();
                this.terms
                    .extend(zip_eq(args.names.clone(), terms.to_owned()));

                this.convert_constraint(&args.parts, heap);

                refinement::NegTyp {
                    arg: refinement::PosTyp,
                    ret: this.convert_pos(ret.clone()),
                }
            }),
        }
    }

    pub fn convert_prop(&self, prop: &Prop) -> refinement::Term {
        prop.convert(&self.terms).make_term()
    }

    pub fn convert_val(&self, val: &Value) -> refinement::Term {
        val.convert(&self.terms).make_term()
    }

    pub fn convert_vals(&self, vals: &[Value]) -> Vec<refinement::Term> {
        vals.iter().map(|x| self.convert_val(x)).collect()
    }

    pub fn convert_constraint(&mut self, parts: &[Constraint], heap: &mut dyn Heap) {
        for part in parts {
            match part {
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
                        mask: FuncTerm::new_bool(move |terms| {
                            let mut this = this.clone();
                            this.terms.extend(zip_eq(names.clone(), terms.to_owned()));
                            this.convert_prop(&cond).to_bool()
                        }),
                    });
                }
                Constraint::Switch(Switch { cond, named, args }) => {
                    let named = self.named.0.get(named).unwrap();

                    heap.switch(refinement::Cond {
                        named: named.clone(),
                        cond: self.convert_prop(cond),
                        args: self.convert_vals(args),
                    })
                }
                Constraint::Assert(cond) => heap.assert(self.convert_prop(cond)),
                Constraint::Builtin(new_name, call) => {
                    let name = call.func.as_ref().unwrap();
                    if name.starts_with('@') {
                        assert_eq!(name, "@byte");
                        let [ptr] = &*call.args else { panic!() };
                        let heap_val = heap.owned(&self.convert_val(ptr), 1, 32);
                        self.terms.insert(new_name.to_owned(), heap_val);
                    } else {
                        let named = self.named.0.get(name).unwrap().upgrade().unwrap();
                        (named.typ.fun)(heap, &self.convert_vals(&call.args));
                    }
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct Desugar<T: Val> {
    pub types: DesugarTypes,
    pub vars: HashMap<String, T>,
    labels: HashMap<String, T::Func>,
}

#[derive(Clone)]
pub struct WeakFuncDef<T: Val> {
    weak: Weak<Lambda<T>>,
    typ: NegTyp,
}

impl<T: Val> Desugar<T> {
    pub fn convert_value(&self, value: &[Value]) -> refinement::Value<T> {
        refinement::Value {
            inj: value.iter().map(|val| val.convert(&self.vars)).collect(),
        }
    }

    pub fn convert_lambda_inner(
        self,
        index: usize,
        names: Vec<String>,
        labels: HashMap<String, WeakFuncDef<T>>,
        block: Rc<Block>,
    ) -> refinement::Lambda<T, impl Fn(&[T]) -> refinement::Expr<T>> {
        refinement::Lambda(PhantomData, move |args: &[T]| -> refinement::Expr<T> {
            let mut this = self.clone();
            for (name, def) in &labels {
                this.labels
                    .insert(name.clone(), T::make(&this, &def.weak, &def.typ));
            }

            for (name, arg) in zip_eq(&names, args) {
                this.vars.insert(name.clone(), arg.clone());
            }

            let Some(step) = block.steps.get(index) else {
                let value = this.convert_value(&block.end.args);
                return match block.end.func.as_ref() {
                    Some(func) => {
                        let label = this.labels.get(func).unwrap();
                        refinement::Expr::Loop(label.clone(), value)
                    }
                    None => refinement::Expr::Return(value),
                };
            };

            match step {
                Stmt::Let(Let { names, bind }) => {
                    let rest = this.convert_lambda(index + 1, &block, None, names.clone());

                    let func_name = bind.func.as_ref().unwrap();
                    let func = if func_name.starts_with('@') {
                        let builtin = match func_name.as_str() {
                            "@read_u8" => refinement::builtin::Builtin::Read,
                            "@write_u8" => refinement::builtin::Builtin::Write,
                            "@alloc" => refinement::builtin::Builtin::Alloc,
                            _ => panic!(),
                        };
                        refinement::Thunk::Builtin(builtin)
                    } else {
                        let local = this.labels.get(func_name).unwrap();
                        refinement::Thunk::Local(local.clone())
                    };
                    let arg = this.convert_value(&bind.args);
                    let bound = refinement::BoundExpr::App(func, arg);

                    refinement::Expr::Let(bound, rest)
                }
                Stmt::FuncDef(FuncDef {
                    name,
                    typ,
                    block: def,
                }) => {
                    let arg_names = typ.args.names.clone();
                    let cont =
                        this.convert_lambda(0, def, Some((name.clone(), typ.clone())), arg_names);

                    let label = T::make(&this, &Rc::downgrade(&cont), typ);
                    this.labels.insert(name.clone(), label.clone());
                    let rest = this.convert_lambda(index + 1, &block, None, vec![]);

                    let bound = refinement::BoundExpr::Cont(cont, label);
                    refinement::Expr::Let(bound, rest)
                }
                Stmt::IfZero(IfZero { val, block: def }) => {
                    let rest = this.convert_lambda(index + 1, &block, None, vec![]);

                    let cont = this.convert_lambda(0, def, None, vec![]);
                    let local = val.convert(&this.vars);
                    refinement::Expr::Match(local, vec![cont, rest])
                }
                Stmt::Unpack(bind) => {
                    let rest = this.convert_lambda(index + 1, &block, None, vec![]);
                    let func = this.types.named.0.get(bind.func.as_ref().unwrap()).unwrap();

                    let arg = this.convert_value(&bind.args);
                    let builtin = refinement::builtin::Builtin::Pack(func.clone(), true);
                    let func = refinement::Thunk::Builtin(builtin);
                    let bound = refinement::BoundExpr::App(func, arg);
                    refinement::Expr::Let(bound, rest)
                }
                Stmt::Pack(bind) => {
                    let rest = this.convert_lambda(index + 1, &block, None, vec![]);
                    let func = this.types.named.0.get(bind.func.as_ref().unwrap()).unwrap();

                    let arg = this.convert_value(&bind.args);
                    let builtin = refinement::builtin::Builtin::Pack(func.clone(), false);
                    let func = refinement::Thunk::Builtin(builtin);
                    let bound = refinement::BoundExpr::App(func, arg);
                    refinement::Expr::Let(bound, rest)
                }
            }
        })
    }

    pub fn convert_lambda(
        &self,
        index: usize,
        block: &Rc<Block>,
        label: Option<(String, NegTyp)>,
        names: Vec<String>,
    ) -> Rc<refinement::Lambda<T>> {
        let func = Rc::new_cyclic(|rec| {
            let mut labels = HashMap::new();
            if let Some((name, typ)) = label.as_ref() {
                let weak_def = WeakFuncDef {
                    // magic to initialize dynamically sized recursive Rc
                    weak: rec.clone() as Weak<Lambda<T>>,
                    typ: typ.clone(),
                };
                labels.insert(name.clone(), weak_def);
            }
            self.clone()
                .convert_lambda_inner(index, names, labels, block.clone())
        });

        func
    }
}

struct Desugared<T: Val> {
    _named: Vec<Rc<refinement::Name>>,
    funcs: HashMap<String, (Rc<Lambda<T>>, refinement::Fun<refinement::NegTyp>)>,
}

impl<T: Val> Desugared<T> {
    fn new(list: LazyNameList, m: &Module) -> Self {
        let types = DesugarTypes::new(list.weak());

        let mut labels = HashMap::new();
        let mut funcs_unique = HashMap::new();

        for def in &m.0 {
            if let Def::Func(func) = def {
                let rc = UninitRc::new();
                let weak = rc.downgrade() as Weak<Lambda<T>>;
                let typ = func.typ.clone();
                labels.insert(func.name.clone(), WeakFuncDef { weak, typ });
                funcs_unique.insert(func.name.clone(), rc);
            }
        }

        let this = Desugar {
            types,
            vars: HashMap::new(),
            labels: HashMap::new(),
        };

        let mut funcs_init = HashMap::new();

        for def in &m.0 {
            if let Def::Func(func) = def {
                let neg = this.types.convert_neg(func.typ.clone());

                let lambda = this.clone().convert_lambda_inner(
                    0,
                    func.typ.args.names.clone(),
                    labels.clone(),
                    func.block.clone(),
                );

                let uninit = funcs_unique.remove(&func.name).unwrap();
                let init = uninit.init(lambda) as Rc<Lambda<T>>;
                funcs_init.insert(func.name.clone(), (init, neg));
            }
        }

        assert!(funcs_unique.is_empty());

        Desugared {
            _named: list.fix(),
            funcs: funcs_init,
        }
    }
}

impl DesugarTypes {
    fn new(list: WeakNameList) -> Self {
        Self {
            named: list,
            terms: HashMap::new(),
        }
    }
}

impl LazyNameList {
    pub fn new(m: &Module) -> Self {
        let mut list = LazyNameList::default();

        for def in &m.0 {
            match def {
                Def::Func(_func) => {}
                Def::Typ(named) => {
                    let NamedConstraint { name, typ } = named.clone();
                    let fun = refinement::Fun {
                        tau: vec![],
                        fun: Rc::new(|_, _| refinement::PosTyp),
                    };

                    let delayed = Box::new(move |named| {
                        let this = DesugarTypes::new(named);
                        let pos = this.convert_pos(typ.clone());
                        refinement::Name::new(pos)
                    });
                    list.0
                        .insert(name, (UniqueRc::new(refinement::Name::new(fun)), delayed));
                }
            }
        }

        list
    }
}

pub fn check(m: &Module) {
    let list = LazyNameList::new(m);
    let this = Desugared::new(list, m);

    for (lambda, neg) in this.funcs.values() {
        let ctx = refinement::SubContext::default();
        ctx.check_expr(lambda, neg);
    }
}

pub fn run(m: Module, name: &str, args: Vec<i32>) -> Vec<i32> {
    let list = LazyNameList::new(&m);
    let this = Desugared::<i32>::new(list, &m);

    let (lambda, _typ) = &this.funcs[name];

    let expr = lambda.inst(&args);
    let mut memory = refinement::eval::Memory::default();
    memory.eval(expr)
}

pub fn convert_neg_builtin(neg: NegTyp) -> refinement::Fun<refinement::NegTyp> {
    let desugar = DesugarTypes {
        named: WeakNameList(Default::default()),
        terms: Default::default(),
    };
    desugar.convert_neg(neg)
}
