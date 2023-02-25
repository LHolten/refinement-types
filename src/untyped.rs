use std::rc::Rc;

// Globally unique
#[derive(Debug, PartialEq, Eq, Hash)]
struct Variant(Rc<()>);

// this defines the shape of a value
// it has holes that can be filled with continuations
enum Pat {
    Sum { variant: Variant, args: Vec<Pat> },
    Hole,
}

// the actual content of a value, it fills the holes of a Pat
enum Subst {
    Vals(Vec<Subst>),
    Con(Rc<Con>),
}

/// selector for a continuation in a Subst
struct Place {
    pos: usize,
    then: MaybePlace,
}
type MaybePlace = Option<Rc<Place>>;

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
struct Value {
    pat: Rc<Pat>,
    subst: Rc<Subst>,
}

// continuations map patterns to programs without environment
struct Con {
    map: Rc<dyn Fn(usize, &Pat) -> Expr>,
}

impl Con {
    fn app_con(&self, offset: usize, pat: &Pat) -> Expr {
        (self.map)(offset, pat)
    }
}

// an actual program, without environment
struct Expr {
    idx: usize,
    place: MaybePlace,
    val: Value,
}

struct Env {
    items: Vec<Rc<Subst>>,
}
impl Env {
    fn lookup(&self, idx: usize, place: &MaybePlace) -> Rc<Con> {
        self.items[idx].app_sub(place)
    }
}

struct Prog {
    env: Env,
    body: Expr,
}

impl Prog {
    fn eval(self) -> Self {
        let Prog { mut env, body } = self;
        let Expr { idx, place, val } = body;
        let body = env.lookup(idx, &place).app_con(idx, &val.pat);

        let mut items = vec![val.subst];
        items.extend(env.items);
        env.items = items;
        Self { env, body }
    }
}

// fn is_even(idx: usize, place: Place, pat: &Pat) -> Expr {
//     match pat {
//         Pat::Z => Expr {
//             idx: idx + 1,
//             place,
//             val: Value {
//                 pat: Rc::new(Pat::TT),
//                 subst: Rc::new(Subst::Nil),
//             },
//         },
//         Pat::S(n) => match n.as_ref() {
//             Pat::Z => Expr {
//                 idx: idx + 1,
//                 place,
//                 val: Value {
//                     pat: Rc::new(Pat::TT),
//                     subst: Rc::new(Subst::Nil),
//                 },
//             },
//             Pat::S(n) => is_even(idx, place, n),
//             _ => panic!(),
//         },
//         _ => panic!(),
//     }
// }

// fn branch(then: Con, other: Con, pat: &Pat) -> Expr {
//     match pat {
//         Pat::TT => todo!(),
//         Pat::FF => todo!(),
//         _ => panic!(),
//     }
// }
// pub fn test() {
//     let prof
// }
