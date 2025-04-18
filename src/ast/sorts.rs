use crate::ast::utils::*;
use crate::parser::Rule;
use crate::parser::*;
use crate::SyGuSParseError;
use pest::iterators::Pair;

use itertools::Itertools;

// Sort = {   Identifier  | "(" ~ Identifier ~ (Sort)+ ~ ")" }

#[derive(Debug, Clone)]
pub enum Sort {
    Simple(Identifier),
    Parameterized(Identifier, Vec<Sort>),
}

impl Sort {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::Sort, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse Sort: {}", s))
        })?;
        Sort::parse(pair)
    }
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
