use super::utils::*;
use super::sorts::*;
use crate::parser::Rule;
use crate::SyGuSParseError;
use itertools::Itertools;
use pest::iterators::Pair;
use pest::Parser;
use crate::parser::SyGuSParser;

#[derive(Debug, Clone)]
pub enum SyGuSTerm {
    Identifier(Identifier),
    Literal(Literal),
    Application(Identifier, Vec<SyGuSTerm>),
    Annotated(Box<SyGuSTerm>, Vec<Attribute>),
    Exists(Vec<SortedVar>, Box<SyGuSTerm>),
    Forall(Vec<SortedVar>, Box<SyGuSTerm>),
    Let(Vec<VarBinding>, Box<SyGuSTerm>),
}

// SyGuSTerm = {
//     Identifier
//   | Literal
//   | "(" ~ Identifier ~ SyGuSTerm+ ~ ")"
//   | "(" ~ "!" ~ SyGuSTerm ~ Attribute+ ~ ")"
//   | "(" ~ "exists" ~ "(" ~ SortedVar+ ~ ")" ~ SyGuSTerm ~ ")"
//   | "(" ~ "forall" ~ "(" ~ SortedVar+ ~ ")" ~ SyGuSTerm ~ ")"
//   | "(" ~ "let" ~ "(" ~ VarBinding+ ~ SyGuSTerm ~ ")" ~ ")"
//   }

impl SyGuSTerm {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SyGuSTerm, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse SyGuSTerm: {}", s))
        })?;
        SyGuSTerm::parse(pair)   
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        // Check if we're already at a SyGuSTerm rule, or need to extract it
        let term_pair = if pair.as_rule() == Rule::SyGuSTerm {
            pair
        } else {
            // Assume this is some parent rule containing a SyGuSTerm
            pair.clone().into_inner().next().ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!(
                    "Expected a SyGuSTerm, but found none in: {:?}",
                    pair
                ))
            })?
        };

        // Process the actual SyGuSTerm
        let inner_pairs = term_pair.into_inner().collect_vec();

        match inner_pairs.as_slice() {
            [pair] if pair.as_rule() == Rule::Identifier => Ok(SyGuSTerm::Identifier(
                parse_identifier(pair.as_str()).unwrap(),
            )),
            [pair] if pair.as_rule() == Rule::Literal => {
                Ok(SyGuSTerm::Literal(Literal::from_str(pair.as_str())))
            }
            // Handle Application (Identifier followed by one or more SyGuSTerm)
            [id_pair, term_pairs @ ..]
                if id_pair.as_rule() == Rule::Identifier && !term_pairs.is_empty() =>
            {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                let terms = term_pairs
                    .iter()
                    .map(|p| SyGuSTerm::parse(p.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
                // println!("Parsed identifier: {:?}", identifier);
                // println!("Parsed terms: {:?}", terms);
                Ok(SyGuSTerm::Application(identifier, terms))
            }

            // Handle Annotated ("!" SyGuSTerm Attribute+)
            [bang, term_pair, attr_pairs @ ..]
                if bang.as_str() == "!" && !attr_pairs.is_empty() =>
            {
                let term = SyGuSTerm::parse(term_pair.clone())?;
                let attributes = attr_pairs
                    .iter()
                    .map(|p| Attribute::parse(p.clone()))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(SyGuSTerm::Annotated(Box::new(term), attributes))
            }

            // Handle Exists ("exists" "(" SortedVar+ ")" SyGuSTerm)
            [exists, vars_container, term_pair] if exists.as_str() == "exists" => {
                let sorted_vars = <Pair<'_, Rule> as Clone>::clone(&vars_container)
                    .into_inner()
                    .map(|p| SortedVar::parse(p))
                    .collect::<Result<Vec<_>, _>>()?;

                let term = SyGuSTerm::parse(term_pair.clone())?;

                Ok(SyGuSTerm::Exists(sorted_vars, Box::new(term)))
            }

            // Handle Forall ("forall" "(" SortedVar+ ")" SyGuSTerm)
            [forall, vars_container, term_pair] if forall.as_str() == "forall" => {
                let sorted_vars = <Pair<'_, Rule> as Clone>::clone(&vars_container)
                    .into_inner()
                    .map(|p| SortedVar::parse(p))
                    .collect::<Result<Vec<_>, _>>()?;

                let term = SyGuSTerm::parse(term_pair.clone())?;

                Ok(SyGuSTerm::Forall(sorted_vars, Box::new(term)))
            }

            // Handle Let ("let" "(" VarBinding+ ")" SyGuSTerm)
            [let_keyword, bindings_container, term_pair] if let_keyword.as_str() == "let" => {
                let var_bindings = <Pair<'_, Rule> as Clone>::clone(&bindings_container)
                    .into_inner()
                    .map(|p| VarBinding::parse(p))
                    .collect::<Result<Vec<_>, _>>()?;
                let term = SyGuSTerm::parse(term_pair.clone())?;
                Ok(SyGuSTerm::Let(var_bindings, Box::new(term)))
            }

            _ => {
                Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unexpected structure in SyGuSTerm parsing: {:?}",
                    inner_pairs
                )))   
            }
        }
    }
}
#[derive(Debug, Clone)]
pub enum SyGuSBfTerm {
    Identifier(Identifier),
    Literal(Literal),
    Application(Identifier, Vec<SyGuSBfTerm>),
    Annotated(Box<SyGuSBfTerm>, Vec<Attribute>),
}

// SyGuSBfTerm = { Identifier | Literal | "(" ~ Identifier ~ SyGuSBfTerm+ ~ ")" | "(" ~ "!" ~ SyGuSBfTerm ~ Attribute+ ~ ")" }
impl SyGuSBfTerm {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SyGuSBfTerm, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse SyGuSBfTerm: {}", s))
        })?;
        SyGuSBfTerm::parse(pair)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [pair] if pair.as_rule() == Rule::Identifier => {
                Ok(SyGuSBfTerm::Identifier(parse_identifier(pair.as_str()).unwrap()))
            }
            [pair] if pair.as_rule() == Rule::Literal => {
                Ok(SyGuSBfTerm::Literal(Literal::from_str(pair.as_str())))
            }
            // Handle Application (Identifier followed by one or more SyGuSBfTerm)
            [id_pair, term_pairs @ ..]
                if id_pair.as_rule() == Rule::Identifier && !term_pairs.is_empty() =>
            {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                let terms = term_pairs
                    .iter()
                    .map(|p| SyGuSBfTerm::parse(p.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
                // println!("Parsed identifier: {:?}", identifier);
                // println!("Parsed terms: {:?}", terms);
                Ok(SyGuSBfTerm::Application(identifier, terms))
            }

            // Handle Annotated ("!" SyGuSBfTerm Attribute+)
            [bang, term_pair, attr_pairs @ ..]
                if bang.as_str() == "!" && !attr_pairs.is_empty() =>
            {
                let term = SyGuSBfTerm::parse(term_pair.clone())?;
                let attributes = attr_pairs
                    .iter()
                    .map(|p| Attribute::parse(p.clone()))
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(SyGuSBfTerm::Annotated(Box::new(term), attributes))
            }

            _ => {
                Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unexpected structure in SyGuSBfTerm parsing: {:?}",
                    inner_pairs
                )))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum SyGuSGTerm {
    Constant(Sort),
    Variable(Sort),
    SyGuSBfTerm(SyGuSBfTerm),
}

// SyGuSGTerm = { "(" ~ "Constant" ~ Sort ~ ")" | "(" ~ "Variable" ~ Sort ~ ")" | SyGuSBfTerm }
impl SyGuSGTerm {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SyGuSGTerm, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse SyGuSGTerm: {}", s))
        })?;
        SyGuSGTerm::parse(pair)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [constant_pair] if constant_pair.as_str() == "Constant" => {
                let sort = Sort::parse(inner_pairs[1].clone())?;
                Ok(SyGuSGTerm::Constant(sort))
            }
            [variable_pair] if variable_pair.as_str() == "Variable" => {
                let sort = Sort::parse(inner_pairs[1].clone())?;
                Ok(SyGuSGTerm::Variable(sort))
            }
            [bf_term_pair] => {
                let bf_term = SyGuSBfTerm::parse(bf_term_pair.clone())?;
                Ok(SyGuSGTerm::SyGuSBfTerm(bf_term))
            }
            _ => {
                Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unexpected structure in SyGuSGTerm parsing: {:?}",
                    inner_pairs
                )))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct GroupedRuleList {
    pub symbol: String,
    pub sort: Sort,
    pub terms: Vec<SyGuSGTerm>,
}

// GroupedRuleList = { "(" ~ Symbol ~ Sort ~ "(" ~ SyGuSGTerm+ ~ ")" ~ ")" }
impl GroupedRuleList {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::GroupedRuleList, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse GroupedRuleList: {}", s))
        })?;
        GroupedRuleList::parse(pair)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        if inner_pairs.len() >= 2 {
            // Extract symbol (should be the first element)
            let symbol = match inner_pairs.get(0).unwrap() {
                sym_pair => parse_identifier(sym_pair.as_str()).ok_or_else(|| {
                    SyGuSParseError::InvalidSyntax(format!(
                        "Expected a symbol, but found: {:?}",
                        sym_pair
                    ))
                })?,
            };

            // Extract sort (should be the second element)
            let sort = match inner_pairs.get(1).unwrap() {
                sort_pair => Sort::parse(sort_pair.clone())?,
            };

            // Collect all terms (could be in a container or individual elements)
            let mut terms = Vec::new();
            for i in 2..inner_pairs.len() {
                let term_pair = &inner_pairs[i];
                // Check if this pair is a container for terms or a term itself
                if term_pair.as_rule() == Rule::SyGuSGTerm {
                    // It's a direct term
                    terms.push(SyGuSGTerm::parse(term_pair.clone())?);
                } else {
                    // Try to extract terms from this container
                    for inner_term in term_pair.clone().into_inner() {
                        if inner_term.as_rule() == Rule::SyGuSGTerm {
                            terms.push(SyGuSGTerm::parse(inner_term)?);
                        }
                    }
                }
            }

            if terms.is_empty() {
                unreachable!(
                    "Expected at least one term in GroupedRuleList, but found none."
                );
            }

            Ok(GroupedRuleList {
                symbol,
                sort,
                terms,
            })
        } else {
            unreachable!(
                "Expected at least two elements in GroupedRuleList parsing, but found: {:?}",
                inner_pairs
            );
        }
    }
}

#[derive(Debug, Clone)]
pub struct GrammarDef {
    pub sorted_vars: Vec<SortedVar>,
    pub grouped_rule_lists: Vec<GroupedRuleList>,
}

impl GrammarDef {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::GrammarDef, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse GrammarDef: {}", s))
        })?;
        GrammarDef::parse(pair)
    }
    // GrammarDef = { ("(" ~ SortedVar+ ~ ")")? ~ "(" ~ GroupedRuleList+ ~ ")" }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        let mut sorted_vars = Vec::new();
        let mut grouped_rule_lists = Vec::new();

        for inner_pair in inner_pairs {
            match inner_pair.as_rule() {
                Rule::SortedVar => {
                    let sorted_var = SortedVar::parse(inner_pair)?;
                    sorted_vars.push(sorted_var);
                }
                Rule::GroupedRuleList => {
                    let grouped_rule_list = GroupedRuleList::parse(inner_pair)?;
                    grouped_rule_lists.push(grouped_rule_list);
                }
                _ => {
                    Err(SyGuSParseError::InvalidSyntax(format!(
                        "Unexpected structure in GrammarDef parsing: {:?}",
                        inner_pair
                    )))?;
                }
            }
        }

        Ok(GrammarDef {
            sorted_vars,
            grouped_rule_lists,
        })
    }
}
