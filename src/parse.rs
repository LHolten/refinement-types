use std::collections::BTreeMap;

use lalrpop_util::lalrpop_mod;

use self::{code::ModuleParser, expr::Module};

pub mod desugar;
pub mod expr;
pub mod types;
lalrpop_mod!(pub code, "/parse/code.rs");

pub fn get_module(code: &str) -> Module {
    let mut map = BTreeMap::new();
    let mut offset = 0;
    for line in code.split_inclusive('\n') {
        map.insert(offset, line);
        offset += line.len();
    }

    match ModuleParser::new().parse(code) {
        Err(e) => {
            let e = e.map_location(|offset| {
                let line_num = map.range(..offset).count();
                let (&start, &line) = map.range(..offset).last().unwrap();
                let char_num = line[..offset - start].chars().count() + 1;
                format!("line {line_num} at {char_num}")
            });
            panic!("{e}")
        }
        Ok(m) => m,
    }
}
