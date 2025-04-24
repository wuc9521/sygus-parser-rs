use std::error::Error;
use derive_more::Display;

#[derive(Debug, Display)]
/// An enumeration representing error conditions encountered during the parsing process of SyGuS files. 
/// It distinguishes between errors produced by the underlying Pest parser, syntax errors detected during parsing, and features not supported by the parser.
/// 
/// This interface enables clear classification of parsing issues by wrapping the original Pest error, or by providing descriptive messages for invalid syntax and unsupported features, thereby facilitating targeted error handling and improved feedback during parsing operations.
pub enum SyGuSParseError {
    #[display(fmt = "Pest parser error: {}", _0)]
    PestError(pest::error::Error<crate::parser::Rule>),
    #[display(fmt = "Invalid syntax: {}", _0)]
    InvalidSyntax(String),
    #[display(fmt = "Unsupported feature: {}", _0)]
    UnsupportedFeature(String),
}




impl Error for SyGuSParseError {}

impl From<pest::error::Error<crate::parser::Rule>> for SyGuSParseError {
    /// Converts an error produced by the underlying Pest parser into the corresponding variant of the custom parsing error type. 
    ///  
    /// 
    /// Maps a given Pest error instance to a unified error representation, allowing the error handling system to consistently process and report issues arising during the parsing of SyGuS files.
    fn from(err: pest::error::Error<crate::parser::Rule>) -> Self {
        SyGuSParseError::PestError(err)
    }
}