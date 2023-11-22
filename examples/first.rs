use structural_types::parse::{desugar::check, get_module};

static CODE: &[&str] = &[include_str!("string.lang"), include_str!("array.lang")];

fn main() {
    for code in CODE {
        let m = get_module(code);
        check(&m)
    }
}
