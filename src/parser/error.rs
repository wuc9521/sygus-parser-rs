use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub enum SyGuSParseError {
    PestError(pest::error::Error<crate::parser::Rule>),
    InvalidSyntax(String),
    UnsupportedFeature(String),
}

impl fmt::Display for SyGuSParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SyGuSParseError::PestError(err) => write!(f, "Pest parser error: {}", err),
            SyGuSParseError::InvalidSyntax(msg) => write!(f, "Invalid syntax: {}", msg),
            SyGuSParseError::UnsupportedFeature(msg) => write!(f, "Unsupported feature: {}", msg),
        }
    }
}


impl Error for SyGuSParseError {}

impl From<pest::error::Error<crate::parser::Rule>> for SyGuSParseError {
    fn from(err: pest::error::Error<crate::parser::Rule>) -> Self {
        SyGuSParseError::PestError(err)
    }
}