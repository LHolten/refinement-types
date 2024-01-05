use miette::IntoDiagnostic;
use mimalloc::MiMalloc;
use std::{env, fs::read, time::Instant};
use structural_types::error::MultiFile;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() -> miette::Result<()> {
    let args: Vec<_> = env::args().collect();
    let [_, file, func, input] = &*args else {
        panic!("not enough arguments")
    };
    let input = read(input).into_diagnostic()?;
    println!("last byte is {}", input.last().unwrap());
    let args = vec![input.len() as i32];

    let source = MultiFile::new(file);
    structural_types::desugar::check(&source);
    println!("typechecking succeeded!");

    let instant = Instant::now();
    let result = structural_types::desugar::run(source, func, args, input);
    println!("the result is {result:?}");
    println!("took: {:.2} seconds", instant.elapsed().as_secs_f32());
    Ok(())
}
