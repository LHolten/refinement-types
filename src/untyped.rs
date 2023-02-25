use std::rc::Rc;

// Globally unique
// TODO: override to use ptr comparisons
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Variant(Rc<()>);

// this defines the shape of a value
// it has holes that can be filled with continuations
enum Pat {
    Sum { variant: Variant, args: Vec<Pat> },
    Hole,
}

// the actual content of a value, it fills the holes of a Pat
pub enum Subst {
    Vals(Vec<Subst>),
    Con(Rc<Con>),
}

/// selector for a continuation in a Subst
pub struct Place {
    pub pos: usize,
    pub then: MaybePlace,
}
pub type MaybePlace = Option<Rc<Place>>;

impl Subst {
    fn app_sub(&self, place: &MaybePlace) -> Rc<Con> {
        match self {
            Subst::Vals(vals) => {
                let Some(Place { pos, then }) = place.as_deref() else {
                    panic!()
                };
                vals[*pos].app_sub(then)
            }
            Subst::Con(con) => {
                assert!(place.is_none());
                con.clone()
            }
        }
    }
}

// The value; it contains a pattern and a substitution
pub struct Value {
    pat: Rc<Pat>,
    subst: Rc<Subst>,
}

// continuations map patterns to programs without environment
pub struct Con {
    pub map: Rc<dyn Fn(&Pat) -> Expr>,
    pub env: Rc<Env>,
}

impl Con {
    fn app_con(&self, pat: &Pat) -> Expr {
        (self.map)(pat)
    }
}

// an actual program, without environment
pub struct Expr {
    pub idx: usize,
    pub place: MaybePlace,
    pub val: Value,
}

pub struct Prog {
    pub env: Rc<Env>,
    pub body: Expr,
}

pub struct Env {
    subst: Rc<Subst>,
    then: MaybeEnv,
}
pub type MaybeEnv = Option<Rc<Env>>;

impl Env {
    fn lookup(&self, idx: usize, place: &MaybePlace) -> Rc<Con> {
        match idx.checked_sub(1) {
            Some(idx) => self.then.unwrap().lookup(idx, place),
            None => self.subst.app_sub(place),
        }
    }
}

impl Prog {
    fn eval(self) -> Self {
        let Prog { mut env, body } = self;
        let Expr { idx, place, val } = body;
        let con = env.lookup(idx, &place);
        let env = Rc::new(Env {
            subst: val.subst,
            then: Some(con.env),
        });
        let body = (con.map)(&val.pat);
        Self { env, body }
    }
}
