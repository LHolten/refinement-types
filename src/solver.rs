use z3::{Config, Context, Solver};

pub fn ctx() -> &'static Context {
    thread_local! {
        static CTX: &'static Context = Box::leak(Box::new(Context::new(&Config::new())));
    }
    CTX.with(Clone::clone)
}

pub fn solver() -> &'static Solver<'static> {
    thread_local! {
        static SOLVER: &'static Solver<'static> = Box::leak(Box::new(Solver::new_for_logic(ctx(), "QF_UFLIA").unwrap()));
    }
    SOLVER.with(Clone::clone)
}
