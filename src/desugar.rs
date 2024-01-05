use std::{
    collections::HashMap,
    marker::PhantomData,
    rc::{Rc, Weak},
};

use self::types::{NameList, Named};
use crate::refinement::{self, Lambda, Val};
use crate::uninit_rc::UninitRc;
use crate::{
    parse::types::{NamedConstraint, NegTyp},
    refinement::Expr,
};
use crate::{
    parse::{code::NegTypParser, types::PosTyp},
    Nested,
};
use crate::{
    parse::{
        expr::{Block, Def, FuncDef, If, Let, Module, Spanned, Stmt, Value},
        lexer::Lexer,
    },
    refinement::builtin::builtins,
};

mod types;
mod value;

#[derive(Clone)]
pub struct Desugar<T: Val> {
    pub types: types::DesugarTypes,
    pub vars: HashMap<String, Nested<T>>,
    labels: HashMap<String, (NegTyp, T::Func)>,
    ret: Rc<Spanned<PosTyp>>,
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
            span: Some(value.source_span(self.types.offset)),
            inj: value_iter.map(|val| val.convert(&self.vars)).collect(),
            scope: Some(self.vars.clone()),
        }
    }

    pub fn convert_expr(mut self, block: &Spanned<Block>) -> refinement::Spanned<Expr<T>> {
        let span = block.source_span(self.types.offset);

        let expr = match &block.val {
            Block::End(bind) => match bind.func.as_ref() {
                Some(func) => {
                    let (_typ, label) = self.labels.get(func).unwrap();
                    let value = self.convert_value(&bind.args);
                    refinement::Expr::Loop(label.clone(), value)
                }
                None => {
                    let value = self.convert_value(&bind.args);
                    refinement::Expr::Return(value)
                }
            },
            Block::Stmt { step, next } => match &step.val {
                Stmt::Debug => {
                    let rest = self.convert_expr(next);
                    refinement::Expr::Debug(Box::new(rest))
                }
                Stmt::Let(Let { names, bind }) => {
                    let func_name = bind.func.as_ref().unwrap();

                    let func = if func_name.starts_with('@') {
                        let builtin = match func_name.as_str() {
                            "@read8" => refinement::builtin::Builtin::Read8,
                            "@read32" => refinement::builtin::Builtin::Read32,
                            "@write8" => refinement::builtin::Builtin::Write8,
                            "@write32" => refinement::builtin::Builtin::Write32,
                            "@alloc" => refinement::builtin::Builtin::Alloc,
                            _ => panic!(),
                        };
                        refinement::Thunk::Builtin(builtin)
                    } else {
                        let (_typ, local) = self.labels.get(func_name).unwrap();
                        refinement::Thunk::Local(local.clone())
                    };

                    let arg = self.convert_value(&bind.args);
                    let rest = self.convert_lambda(next, None, names);
                    refinement::Expr::App(func, arg, rest)
                }
                Stmt::FuncDef(FuncDef {
                    name,
                    typ,
                    block: def,
                }) => {
                    let arg_names = &typ.args.val.names;
                    let cont =
                        self.convert_lambda(def, Some((name.clone(), typ.clone())), arg_names);

                    let label = T::make(&self, &Rc::downgrade(&cont), typ);
                    self.labels
                        .insert(name.clone(), (typ.clone(), label.clone()));
                    let rest = self.convert_expr(next);

                    refinement::Expr::Cont(cont, label, Box::new(rest))
                }
                Stmt::If(If { val, block: def }) => {
                    let local = val.convert(&self.vars);
                    let rest = self.clone().convert_expr(next);
                    let cont = self.convert_expr(def);
                    refinement::Expr::Match(local, vec![rest, cont])
                }
            },
        };
        refinement::Spanned { span, val: expr }
    }

    pub fn convert_lambda_inner(
        self,
        names: &[String],
        labels: HashMap<String, WeakFuncDef<T>>,
        block: Rc<Spanned<Block>>,
    ) -> refinement::Lambda<T, impl Fn(&[T]) -> refinement::Spanned<refinement::Expr<T>>> {
        let names = names.to_owned();
        let func = move |args: &[T]| -> refinement::Spanned<refinement::Expr<T>> {
            let mut this = self.clone();
            for (name, def) in &labels {
                let label = T::make(&this, &def.weak, &def.typ);
                this.labels.insert(name.clone(), (def.typ.clone(), label));
            }

            this.vars.extend(this.types.consume_args(args, &names));
            this.convert_expr(&block)
        };
        refinement::Lambda {
            _val: PhantomData,
            func,
        }
    }

    pub fn convert_lambda(
        &self,
        block: &Rc<Spanned<Block>>,
        label: Option<(String, NegTyp)>,
        names: &[String],
    ) -> Rc<refinement::Lambda<T>> {
        let func = Rc::new_cyclic(|rec| {
            let mut labels = HashMap::new();
            let mut this = self.clone();
            if let Some((name, typ)) = label.as_ref() {
                let weak_def = WeakFuncDef {
                    // magic to initialize dynamically sized recursive Rc
                    weak: rec.clone() as Weak<Lambda<T>>,
                    typ: typ.clone(),
                };
                labels.insert(name.clone(), weak_def);
                this.ret = typ.ret.clone();
            }
            this.convert_lambda_inner(names, labels, block.clone())
        });

        func
    }
}

struct Desugared<T: Val> {
    funcs: HashMap<String, (Rc<Lambda<T>>, refinement::Fun<refinement::NegTyp>)>,
}

impl<T: Val> Desugared<T> {
    fn new(list: NameList, m: &Module) -> Self {
        let offset = builtins().iter().map(|x| x.len()).sum();
        let types = types::DesugarTypes::new(list, offset);

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

        let mut funcs_init = HashMap::new();

        for def in &m.0 {
            if let Def::Func(func) = def {
                let this = Desugar {
                    types: types.clone(),
                    vars: HashMap::new(),
                    labels: HashMap::new(),
                    ret: func.typ.ret.clone(),
                };

                let neg = this.types.convert_neg(func.typ.clone());

                let lambda = this.clone().convert_lambda_inner(
                    &func.typ.args.val.names,
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

pub fn convert_neg(files: &[&str], idx: usize) -> refinement::Fun<refinement::NegTyp> {
    let lexer = Lexer::new(files[idx]);
    let offset = files.iter().take(idx).map(|x| x.len()).sum();
    let parsed = NegTypParser::new().parse(lexer).unwrap();

    let desugar = types::DesugarTypes {
        named: NameList(Default::default()),
        terms: Default::default(),
        exactly: Default::default(),
        offset,
    };
    desugar.convert_neg(parsed)
}
