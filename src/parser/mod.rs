pub mod error;
pub use error::*;
pub use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar = "parser/sygus.v2.pest"]
pub struct SyGuSParser;
pub type Error = pest::error::Error<Rule>;