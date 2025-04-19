use crate::ast::utils::*;
use crate::parser::Rule;
use crate::parser::*;
use crate::SyGuSParseError;
use pest::iterators::Pair;

use itertools::Itertools;

// Sort = {   Identifier  | "(" ~ Identifier ~ (Sort)+ ~ ")" }

#[derive(Debug, Clone)]
/// Represents an abstract sort used in the SyGuS language specification. 
/// This type differentiates between a simple sort, defined solely by an identifier, and a parameterized sort that couples an identifier with a collection of sub-sorts.
pub enum Sort {
    Simple(Identifier),
    Parameterized(Identifier, Vec<Sort>),
}

impl Sort {
    /// Parses a string slice representing a sort into its corresponding internal representation, returning either the parsed result or an error. 
    /// 
    /// 
    /// Converts the provided string into an abstract syntax tree element according to the SyGuS standard by invoking the underlying parser and handling the first parsed element. 
    /// This function validates that the input conforms to the expected sort format and encapsulates any parsing issues within a standardized error type.
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::Sort, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse Sort: {}", s))
        })?;
        Sort::parse(pair)
    }
    /// Parses an input pair into the corresponding sort representation. 
    /// 
    /// This function converts a parse tree pair into a syntactic sort, handling both simple and parameterized forms. 
    /// It inspects the inner pairs of the provided pair and, if a single identifier is encountered, returns the simple variant; otherwise, it recursively parses any additional sort pairs to construct the parameterized variant. 
    /// If the structure does not match the expected patterns, it returns a syntax error with details of the mismatched input.
    /// 
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [id_pair] if id_pair.as_rule() == Rule::Identifier => {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                Ok(Sort::Simple(identifier))
            }
            [id_pair, sort_pairs @ ..] if id_pair.as_rule() == Rule::Identifier => {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                let sorts = sort_pairs
                    .iter()
                    .map(|pair| Sort::parse(pair.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Sort::Parameterized(identifier, sorts))
            }
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Expected Sort, found: {:?}",
                inner_pairs
            ))),
        }
    }
}
