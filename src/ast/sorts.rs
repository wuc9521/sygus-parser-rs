use crate::ast::common::*;
use crate::parser::Rule;
use pest::iterators::Pair;

use itertools::Itertools;

// Sort = {   Identifier  | "(" ~ Identifier ~ (Sort)+ ~ ")" }

#[derive(Debug, Clone)]
pub enum Sort {
    Simple(Identifier),
    Parameterized(Identifier, Vec<Sort>),
}

impl Sort {
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, crate::parser::Error> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [id_pair] if id_pair.as_rule() == Rule::Identifier => {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                // println!("Parsed identifier: {:?}", identifier);
                Ok(Sort::Simple(identifier))
            }
            [id_pair, sort_pairs @ ..] if id_pair.as_rule() == Rule::Identifier => {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                // println!("Parsed identifier: {:?}", identifier);
                let sorts = sort_pairs
                    .iter()
                    .map(|pair| Sort::parse(pair.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Sort::Parameterized(identifier, sorts))
            }
            _ => unreachable!("Unexpected sort structure: {:?}", inner_pairs),
        }
    }
}
