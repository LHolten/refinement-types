use std::{
    collections::HashMap,
    marker::PhantomData,
    rc::{Rc, Weak},
};

use self::types::{NameList, Named};
use crate::parse::code::NegTypParser;
use crate::parse::expr::{Block, Def, FuncDef, If, Let, Module, Spanned, Stmt, Value};
use crate::parse::types::{NamedConstraint, NegTyp};
use crate::refinement::{self, typing::zip_eq, Lambda, Val};
use crate::uninit_rc::UninitRc;

mod types;
mod value;

#[derive(Clone)]
pub struct Desugar<T: Val> {
    pub types: types::DesugarTypes,
    pub vars: HashMap<String, T>,
    labels: HashMap<String, T::Func>,
}

#[derive(Clone)]
pub struct WeakFuncDef<T: Val> {
    weak: Weak<Lambda<T>>,
    typ: NegTyp,
}

impl<T: Val> Desugar<T> {
    pub fn convert_value(&self, value: &Spanned<Vec<Value>>) -> refinement::Value<T> {
        let value_iter = value.val.iter();
        refinement::Value {
            span: Some(value.source_span()),
            inj: value_iter.map(|val| val.convert(&self.vars)).collect(),
        }
    }

    pub fn convert_lambda_inner(
        self,
        names: Vec<String>,
        labels: HashMap<String, WeakFuncDef<T>>,
        block: Rc<Spanned<Block>>,
    ) -> refinement::Lambda<T, impl Fn(&[T]) -> refinement::Expr<T>> {
        let span = block.source_span();

        let func = move |args: &[T]| -> refinement::Expr<T> {
            let mut this = self.clone();
            for (name, def) in &labels {
                this.labels
                    .insert(name.clone(), T::make(&this, &def.weak, &def.typ));
            }

            for (name, arg) in zip_eq(&names, args) {
                this.vars.insert(name.clone(), arg.clone());
            }

            match &block.val {
                Block::End(bind) => {
                    let value = this.convert_value(&bind.args);
                    match bind.func.as_ref() {
                        Some(func) => {
                            let label = this.labels.get(func).unwrap();
                            refinement::Expr::Loop(label.clone(), value)
                        }
                        None => refinement::Expr::Return(value),
                    }
                }
                Block::Stmt { step, next } => match &step.val {
                    Stmt::Let(Let { names, bind }) => {
                        let rest = this.convert_lambda(next, None, names.clone());

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
                        let arg_names = typ.args.val.names.clone();
                        let cont =
                            this.convert_lambda(def, Some((name.clone(), typ.clone())), arg_names);

                        let label = T::make(&this, &Rc::downgrade(&cont), typ);
                        this.labels.insert(name.clone(), label.clone());
                        let rest = this.convert_lambda(next, None, vec![]);

                        let bound = refinement::BoundExpr::Cont(cont, label);
                        refinement::Expr::Let(bound, rest)
                    }
                    Stmt::If(If { val, block: def }) => {
                        let rest = this.convert_lambda(next, None, vec![]);

                        let cont = this.convert_lambda(def, None, vec![]);
                        let local = val.convert(&this.vars);
                        refinement::Expr::Match(local, vec![rest, cont])
                    }
                    Stmt::Unpack(bind) => {
                        let rest = this.convert_lambda(next, None, vec![]);
                        let named = this.types.named.0.get(bind.func.as_ref().unwrap()).unwrap();
                        let named = this.types.convert_named(named);

                        let typ = refinement::Fun {
                            tau: vec![],
                            span: named.typ.span,
                            fun: Rc::new(move |heap, terms| {
                                let once = refinement::Once {
                                    named: named.clone(),
                                    args: terms.to_owned(),
                                    span: None,
                                };
                                heap.once(once, None)?;

                                let terms = terms.to_owned();
                                let named = named.clone();
                                let ret = refinement::Fun {
                                    tau: vec![],
                                    span: named.typ.span,
                                    fun: Rc::new(move |heap, _| {
                                        (named.typ.fun)(heap, &terms)?;

                                        Ok(refinement::PosTyp)
                                    }),
                                };

                                Ok(refinement::NegTyp {
                                    arg: refinement::PosTyp,
                                    ret,
                                })
                            }),
                        };

                        let builtin = refinement::builtin::Builtin::Pack(typ);
                        let func = refinement::Thunk::Builtin(builtin);
                        let arg = this.convert_value(&bind.args);
                        let bound = refinement::BoundExpr::App(func, arg);
                        refinement::Expr::Let(bound, rest)
                    }
                    Stmt::Pack(bind) => {
                        let rest = this.convert_lambda(next, None, vec![]);
                        let named = this.types.named.0.get(bind.func.as_ref().unwrap()).unwrap();

                        let named = this.types.convert_named(named);

                        let typ = refinement::Fun {
                            tau: vec![],
                            span: named.typ.span,
                            fun: Rc::new(move |heap, terms| {
                                (named.typ.fun)(heap, terms)?;

                                let terms = terms.to_owned();
                                let named = named.clone();
                                let ret = refinement::Fun {
                                    tau: vec![],
                                    span: named.typ.span,
                                    fun: Rc::new(move |heap, _| {
                                        let once = refinement::Once {
                                            named: named.clone(),
                                            args: terms.clone(),
                                            span: None,
                                        };
                                        heap.once(once, None)?;

                                        Ok(refinement::PosTyp)
                                    }),
                                };

                                Ok(refinement::NegTyp {
                                    arg: refinement::PosTyp,
                                    ret,
                                })
                            }),
                        };

                        let builtin = refinement::builtin::Builtin::Pack(typ);
                        let func = refinement::Thunk::Builtin(builtin);
                        let arg = this.convert_value(&bind.args);
                        let bound = refinement::BoundExpr::App(func, arg);
                        refinement::Expr::Let(bound, rest)
                    }
                },
            }
        };
        refinement::Lambda {
            _val: PhantomData,
            span,
            func,
        }
    }

    pub fn convert_lambda(
        &self,
        block: &Rc<Spanned<Block>>,
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
                .convert_lambda_inner(names, labels, block.clone())
        });

        func
    }
}

struct Desugared<T: Val> {
    funcs: HashMap<String, (Rc<Lambda<T>>, refinement::Fun<refinement::NegTyp>)>,
}

impl<T: Val> Desugared<T> {
    fn new(list: NameList, m: &Module) -> Self {
        let types = types::DesugarTypes::new(list);

        let mut labels = HashMap::new();
        let mut funcs_uninit = HashMap::new();

        for def in &m.0 {
            if let Def::Func(func) = def {
                let rc = UninitRc::new();
                let weak = rc.downgrade() as Weak<Lambda<T>>;
                let typ = func.typ.clone();
                labels.insert(func.name.clone(), WeakFuncDef { weak, typ });
                funcs_uninit.insert(func.name.clone(), rc);
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
                    func.typ.args.val.names.clone(),
                    labels.clone(),
                    func.block.clone(),
                );

                let uninit = funcs_uninit.remove(&func.name).unwrap();
                let init = uninit.init(lambda) as Rc<Lambda<T>>;
                funcs_init.insert(func.name.clone(), (init, neg));
            }
        }

        assert!(funcs_uninit.is_empty());

        Desugared { funcs: funcs_init }
    }
}

impl NameList {
    pub fn new(m: &Module) -> Self {
        let mut list = NameList::default();

        for def in &m.0 {
            match def {
                Def::Func(_func) => {}
                Def::Typ(named) => {
                    let NamedConstraint { name, typ } = named.clone();
                    list.0.insert(name, Named::new(typ));
                }
            }
        }

        list
    }
}

pub fn check(m: &Module) -> miette::Result<()> {
    let list = NameList::new(m);
    let this = Desugared::new(list, m);

    for (lambda, neg) in this.funcs.values() {
        let ctx = refinement::SubContext::default();
        ctx.check_expr(lambda, neg)?;
    }
    Ok(())
}

pub fn run(m: Module, name: &str, args: Vec<i32>, heap: Vec<u8>) -> Vec<i32> {
    let list = NameList::new(&m);
    let this = Desugared::<i32>::new(list, &m);

    let (lambda, _typ) = &this.funcs[name];

    let expr = lambda.inst(&args);
    let mut memory = refinement::eval::Memory::new(heap);
    memory.eval(expr.val)
}

pub fn convert_neg_builtin(neg: NegTyp) -> refinement::Fun<refinement::NegTyp> {
    let desugar = types::DesugarTypes {
        named: NameList(Default::default()),
        terms: Default::default(),
        exactly: Default::default(),
    };
    desugar.convert_neg(neg)
}

pub fn convert_neg(code: &str) -> refinement::Fun<refinement::NegTyp> {
    let parsed = NegTypParser::new().parse(code).unwrap();
    convert_neg_builtin(parsed)
}
