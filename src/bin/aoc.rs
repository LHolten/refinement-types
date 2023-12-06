use miette::IntoDiagnostic;
use mimalloc::MiMalloc;
use std::{
    env,
    fs::{read, File},
    io::Read,
    time::Instant,
};

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

    let mut file = File::open(file).unwrap();
    let mut code = String::new();
    file.read_to_string(&mut code).unwrap();

    let m = structural_types::parse::get_module(&code);
    if let Err(err) = structural_types::desugar::check(&m) {
        return Err(err.with_source_code(code));
    };

    println!("typechecking succeeded!");
    let instant = Instant::now();
    let result = structural_types::desugar::run(m, func, args, input);
    println!("the result is {result:?}");
    println!("took: {:.2} seconds", instant.elapsed().as_secs_f32());
    Ok(())
}
