use lalrpop_util::lalrpop_mod;

pub mod desugar;
pub mod expr;
pub mod types;
lalrpop_mod!(pub code, "/parse/code.rs");
