use std::rc::Rc;

// Globally unique
// TODO: override to use ptr comparisons
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Variant(Rc<()>);

// The value; it contains a pattern and a substitution
pub struct Value {
    pub pat: Vec<Variant>,
    pub subst: Vec<Con>,
}

// continuations map patterns to programs without environment
pub struct Con {
    pub map: Rc<dyn Fn(&[Variant]) -> Expr>,
}

// an actual program, without environment
pub struct Expr {
    pub idx: usize,
    pub val: Value,
}

pub struct Prog {
    pub env: Vec<Con>,
    pub body: Expr,
}

impl Prog {
    fn eval(self) -> Self {
        let Prog { mut env, body } = self;
        let Expr { idx, val } = body;
        env.truncate(env.len() - idx);
        let con = env.pop().unwrap();
        env.extend(val.subst);
        let body = (con.map)(&val.pat);
        Self { env, body }
    }
}

fn selfapp(pat: &[Variant]) -> Expr {
    Expr {
        idx: 0,
        val: Value {
            pat: vec![],
            subst: vec![Con {
                map: Rc::new(selfapp),
            }],
        },
    }
}
