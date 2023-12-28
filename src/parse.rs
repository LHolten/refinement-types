use std::process::exit;

use lalrpop_util::{lalrpop_mod, ParseError};
use miette::{Diagnostic, Report, SourceSpan};
use thiserror::Error;

use self::{
    code::ModuleParser,
    expr::Module,
    lexer::{Lexer, LexicalError, Token},
};

pub mod expr;
pub mod lexer;
pub mod types;
lalrpop_mod!(pub code, "/parse/code.rs");

pub fn get_module(code: &str) -> Module {
    let lexer = Lexer::new(code);
    match ModuleParser::new().parse(lexer) {
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

    #[error(transparent)]
    #[diagnostic(transparent)]
    User(LexicalError),
}

impl From<ParseError<usize, Token, LexicalError>> for ParseErr {
    fn from(value: ParseError<usize, Token, LexicalError>) -> Self {
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
                name: format!("{:?}", token.1),
                location: (token.0, token.2 - token.0).into(),
                expected: format!("expected one of: {}", expected.join(", ")),
            },
            ParseError::ExtraToken { token } => ParseErr::UnrecognizedToken {
                name: format!("{:?}", token.1),
                location: (token.0, token.2 - token.0).into(),
                expected: "expected end of file".to_owned(),
            },
            ParseError::User { error } => ParseErr::User(error),
        }
    }
}
