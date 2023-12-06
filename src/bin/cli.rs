use mimalloc::MiMalloc;
use std::{env, fs::File, io::Read};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> miette::Result<()> {
    let args: Vec<_> = env::args().collect();
    let [_, file, func, args @ ..] = &*args else {
        panic!("not enough arguments")
    };
    let args = args.iter().map(|x| x.parse().unwrap()).collect();
    let mut file = File::open(file).unwrap();
    let mut code = String::new();
    file.read_to_string(&mut code).unwrap();
    let m = structural_types::parse::get_module(&code);
    if let Err(err) = structural_types::desugar::check(&m) {
        return Err(err.with_source_code(code));
    };
    let result = structural_types::desugar::run(m, func, args, vec![]);
    println!("the result is {result:?}");
    Ok(())
}
