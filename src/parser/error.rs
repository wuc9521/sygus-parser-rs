use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub enum ParseError {
    PestError(pest::error::Error<crate::parser::Rule>),
    InvalidSyntax(String),
    UnsupportedFeature(String),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::PestError(err) => write!(f, "Pest parser error: {}", err),
            ParseError::InvalidSyntax(msg) => write!(f, "Invalid syntax: {}", msg),
            ParseError::UnsupportedFeature(msg) => write!(f, "Unsupported feature: {}", msg),
        }
    }
}


impl Error for ParseError {}

impl From<pest::error::Error<crate::parser::Rule>> for ParseError {
    fn from(err: pest::error::Error<crate::parser::Rule>) -> Self {
        ParseError::PestError(err)
    }
}

pub type Result<T> = std::result::Result<T, ParseError>;