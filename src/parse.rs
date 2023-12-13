use std::process::exit;

use lalrpop_util::{lalrpop_mod, lexer::Token, ParseError};
use miette::{Diagnostic, Report, SourceSpan};
use thiserror::Error;

use self::{code::ModuleParser, expr::Module};

pub mod expr;
pub mod types;
lalrpop_mod!(pub code, "/parse/code.rs");

pub fn get_module(code: &str) -> Module {
    match ModuleParser::new().parse(code) {
        Err(e) => {
            let report = Report::from(ParseErr::from(e));
            let e = report.with_source_code(code.to_owned());
            println!("{e:?}");
            exit(1)
        }
        Ok(m) => m,
    }
}

#[derive(Debug, Diagnostic, Error)]
pub enum ParseErr {
    #[error("Token is invalid")]
    InvalidToken {
        #[label]
        location: SourceSpan,
    },

    #[error("Unexpected token: {name}")]
    UnrecognizedToken {
        name: String,
        #[label]
        location: SourceSpan,
        #[help]
        expected: String,
    },

    #[error("{0}")]
    User(&'static str),
}

impl From<ParseError<usize, Token<'_>, &'static str>> for ParseErr {
    fn from(value: ParseError<usize, Token<'_>, &'static str>) -> Self {
        match value {
            ParseError::InvalidToken { location } => ParseErr::InvalidToken {
                location: (location, 0).into(),
            },
            ParseError::UnrecognizedEof { location, expected } => ParseErr::UnrecognizedToken {
                name: "end of file".to_owned(),
                location: (location, 0).into(),
                expected: format!("expected one of: {}", expected.join(", ")),
            },
            ParseError::UnrecognizedToken { token, expected } => ParseErr::UnrecognizedToken {
                name: token.1.to_string(),
                location: (token.0, token.2 - token.0).into(),
                expected: format!("expected one of: {}", expected.join(", ")),
            },
            ParseError::ExtraToken { token } => ParseErr::UnrecognizedToken {
                name: token.1.to_string(),
                location: (token.0, token.2 - token.0).into(),
                expected: "expected end of file".to_owned(),
            },
            ParseError::User { error } => ParseErr::User(error),
        }
    }
}
