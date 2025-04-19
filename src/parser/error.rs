use std::error::Error;
use std::fmt;

#[derive(Debug)]
/// An enumeration representing error conditions encountered during the parsing process of SyGuS files. 
/// It distinguishes between errors produced by the underlying Pest parser, syntax errors detected during parsing, and features not supported by the parser.
/// 
/// This interface enables clear classification of parsing issues by wrapping the original Pest error, or by providing descriptive messages for invalid syntax and unsupported features, thereby facilitating targeted error handling and improved feedback during parsing operations.
pub enum SyGuSParseError {
    PestError(pest::error::Error<crate::parser::Rule>),
    InvalidSyntax(String),
    UnsupportedFeature(String),
}

impl fmt::Display for SyGuSParseError {
    /// Formats an error instance into a human-readable message by matching against its internal variants. 
    /// 
    /// 
    /// This functionality renders distinct messages for different error cases, such as errors originating from the underlying Pest parser, invalid syntax issues, or unsupported features, by writing appropriately formatted text to the provided formatter.
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
    /// Converts an error produced by the underlying Pest parser into the corresponding variant of the custom parsing error type. 
    ///  
    /// 
    /// Maps a given Pest error instance to a unified error representation, allowing the error handling system to consistently process and report issues arising during the parsing of SyGuS files.
    fn from(err: pest::error::Error<crate::parser::Rule>) -> Self {
        SyGuSParseError::PestError(err)
    }
}