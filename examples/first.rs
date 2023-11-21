use std::collections::BTreeMap;

use structural_types::parse::code::ModuleParser;

static CODE: &str = include_str!("first.lang");

fn main() {
    let mut map = BTreeMap::new();
    let mut offset = 0;
    for line in CODE.split_inclusive('\n') {
        map.insert(offset, line);
        offset += line.len();
    }

    match ModuleParser::new().parse(CODE) {
        Err(e) => {
            let e = e.map_location(|offset| {
                let line_num = map.range(..offset).count();
                let (&start, &line) = map.range(..offset).last().unwrap();
                let char_num = line[..offset - start].chars().count() + 1;
                format!("line {line_num} at {char_num}")
            });
            println!("{e}")
        }
        Ok(m) => {
            structural_types::parse::desugar::Desugar::check(m);
        }
    }
}
