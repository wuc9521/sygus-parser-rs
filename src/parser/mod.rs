pub mod error;
pub use error::*;
pub use pest::Parser;

#[derive(pest_derive::Parser)]
#[grammar = "parser/sygus.v2.pest"]
/// A custom parser configured with Pest's procedural macro to process SyGuS files is provided. 
/// This parser leverages a designated grammar file to define the syntax rules for SyGuS v2.1, allowing users to parse and validate inputs structured according to the SyGuS specification.
pub struct SyGuSParser;
pub type Error = pest::error::Error<Rule>;