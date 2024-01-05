use lalrpop_util::{lalrpop_mod, ParseError};
use miette::{Diagnostic, SourceSpan};
use thiserror::Error;

use crate::error::MultiFile;

use self::{
    code::ModuleParser,
    expr::Module,
    lexer::{Lexer, LexicalError, Token},
};

pub mod expr;
pub mod lexer;
pub mod types;
lalrpop_mod!(pub code, "/parse/code.rs");

impl MultiFile {
    pub fn get_module(&self) -> Module {
        let lexer = Lexer::new(&self.code, self.offset());
        let parse = ModuleParser::new().parse(lexer);
        self.unwrap(parse.map_err(ParseErr::from))
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
