use mimalloc::MiMalloc;
use std::env;
use structural_types::error::MultiFile;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> miette::Result<()> {
    let args: Vec<_> = env::args().collect();
    let [_, file, func, args @ ..] = &*args else {
        panic!("not enough arguments")
    };
    let args = args.iter().map(|x| x.parse().unwrap()).collect();

    let source = MultiFile::new(file);
    structural_types::desugar::check(&source);
    let result = structural_types::desugar::run(source, func, args, vec![]);
    println!("the result is {result:?}");
    Ok(())
}
