use logos::{Logos, SpannedIter};
use miette::{Diagnostic, SourceSpan};

#[derive(Clone, Logos, Debug, PartialEq)]
#[logos(skip r"[ \t\n\f]+")]
#[logos(skip r"//.*")]
pub enum Token {
    #[regex("[@]?[_a-zA-Z][_a-zA-Z0-9]*", |lex| lex.slice().to_owned())]
    Var(String),
    #[regex(r"\d+", |lex| lex.slice().parse::<i32>().unwrap())]
    #[regex(r"'\d'", |lex| lex.slice().as_bytes()[1] as i32)]
    #[regex(r"'\\n'", |_lex| 10)]
    Num(i32),
    #[token("=")]
    Assign,
    #[token(":")]
    Colon,
    #[token("->")]
    Arrow,
    #[token(".")]
    Period,
    #[token(",")]
    Comma,
    #[token(";")]
    Semi,
    #[token("+")]
    Add,
    #[token("-")]
    Sub,
    #[token("*")]
    Mul,
    #[token("%")]
    Mod,
    #[token("/")]
    Div,
    #[token("<<")]
    Shl,
    #[token(">>")]
    Shr,
    #[token("<")]
    Less,
    #[token("<=")]
    LessEq,
    #[token("==")]
    Eq,
    #[token("!=")]
    NotEq,
    #[token("&&")]
    And,
    #[token("||")]
    Or,
    #[token("*?")]
    MulSafe,
    #[token("+?")]
    AddSafe,
    #[token("{")]
    BraceL,
    #[token("}")]
    BraceR,
    #[token("(")]
    ParenL,
    #[token(")")]
    ParenR,
    #[token("[")]
    SquareL,
    #[token("]")]
    SquareR,
    #[token("fn")]
    FnKeyword,
    #[token("loop")]
    LoopKeyword,
    #[token("if")]
    IfKeyword,
    #[token("for")]
    ForKeyword,
    #[token("type")]
    TypeKeyword,
    #[token("where")]
    WhereKeyword,
    #[token("assert")]
    AssertKeyword,
    #[token("let")]
    LetKeyword,
    #[token("return")]
    ReturnKeyword,
    #[token("#debug")]
    DebugKeyword,
}

#[derive(Debug, Diagnostic, thiserror::Error)]
#[error("token is invalid")]
pub struct LexicalError {
    #[label]
    span: SourceSpan,
}

pub struct Lexer<'input> {
    offset: usize,
    token_stream: SpannedIter<'input, Token>,
}

impl<'input> Lexer<'input> {
    pub fn new(input: &'input str, offset: usize) -> Self {
        Self {
            token_stream: Token::lexer(input).spanned(),
            offset,
        }
    }
}

impl<'input> Iterator for Lexer<'input> {
    type Item = Result<(usize, Token, usize), LexicalError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.token_stream.next().map(|(token, span)| match token {
            Err(()) => Err(LexicalError {
                span: (self.offset + span.start, span.end - span.start).into(),
            }),
            Ok(token) => Ok((self.offset + span.start, token, self.offset + span.end)),
        })
    }
}
