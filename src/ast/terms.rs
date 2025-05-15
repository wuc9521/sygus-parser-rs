use super::sorts::*;
use super::utils::*;
use crate::parser::Rule;
use crate::parser::SyGuSParser;
use crate::SyGuSParseError;
use derive_more::Display;
use itertools::Itertools;
use pest::iterators::Pair;
use pest::Parser;

#[derive(Debug, Clone, Display, PartialEq)]
/// Represents the various syntactic forms that can occur within a SyGuS term.
/// This enumeration abstracts the building blocks of SyGuS expressions into distinct variants, ranging from simple identifiers and literals to composite forms like applications, annotated expressions, quantifiers (exists and forall), and let bindings.
pub enum SyGuSTerm {
    #[display(fmt = "{}", _0)] // Identifier
    Identifier(Identifier),
    #[display(fmt = "{}", _0)] // Literal
    Literal(Literal),
    #[display(
        fmt = "({} {})",
        _0,
        "_1.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(\" \")"
    )] // (Identifier followed by one or more SyGuSTerm)
    Application(Identifier, Vec<SyGuSTerm>),

    #[display(
        fmt = "(! {} {})",
        _0,
        "_1.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(\" \")"
    )] // ("!" SyGuSTerm Attribute+)
    Annotated(Box<SyGuSTerm>, Vec<Attribute>),

    #[display(
        fmt = "(exists {} {})",
        "_0.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(\" \")",
        _1
    )] // ("exists" "(" SortedVar+ ")" SyGuSTerm)
    Exists(Vec<SortedVar>, Box<SyGuSTerm>),

    #[display(
        fmt = "(forall {} {})",
        "_0.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(\" \")",
        _1
    )] // ("forall" "(" SortedVar+ ")" SyGuSTerm)
    Forall(Vec<SortedVar>, Box<SyGuSTerm>),

    #[display(
        fmt = "(let {} {})",
        "_0.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(\" \")",
        _1
    )] // ("let" "(" VarBinding+ ")" SyGuSTerm)
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
    /// Parses a string slice into an abstract representation of a SyGuS term.
    ///
    /// This method attempts to convert the provided input string into a structured term by invoking the parser with the designated rule.
    /// If parsing is successful, it returns the corresponding term structure; otherwise, it produces a syntax error detailing the failure encountered during conversion.
    ///
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SyGuSTerm, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse SyGuSTerm: {}", s))
            })?;
        SyGuSTerm::parse(pair)
    }
    /// Parses a pest parse tree element into a corresponding syntactic representation following the SyGuS term grammar.
    ///
    ///
    /// Identifies and converts input based on its structure, recursively handling constructs such as identifiers, literals, applications, annotated expressions, existential and universal quantifications, as well as let bindings.
    /// Returns a Result wrapping the appropriate syntactic variant or an error if the input structure deviates from the expected SyGuS term productions.
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
                Identifier::from_str(pair.as_str()).unwrap(),
            )),
            [pair] if pair.as_rule() == Rule::Literal => {
                Ok(SyGuSTerm::Literal(Literal::from_str(pair.as_str())))
            }
            // Handle Application (Identifier followed by one or more SyGuSTerm)
            [id_pair, term_pairs @ ..]
                if id_pair.as_rule() == Rule::Identifier && !term_pairs.is_empty() =>
            {
                let identifier = Identifier::from_str(id_pair.as_str()).unwrap();
                let terms = term_pairs
                    .iter()
                    .map(|p| SyGuSTerm::parse(p.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
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

            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Unexpected structure in SyGuSTerm parsing: {:?}",
                inner_pairs
            ))),
        }
    }
}
#[derive(Debug, Clone, Display)]
/// Represents a basic term in SyGuS grammar that can be an identifier, a literal, an application, or an annotated term.
///
///
/// Encapsulates four distinct variants: one for a simple identifier, another for a literal value, one for an application where an identifier is applied to a non-empty list of basic terms, and one for an annotated term that couples a basic term with one or more attributes.
pub enum SyGuSBfTerm {
    #[display(fmt = "{}", _0)] // Identifier
    Identifier(Identifier),

    #[display(fmt = "{}", _0)] // Literal
    Literal(Literal),

    #[display(
        fmt = "({} {})",
        _0,
        "_1.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")"
    )] // (Identifier followed by one or more SyGuSBfTerm)
    Application(Identifier, Vec<SyGuSBfTerm>),

    #[display(
        fmt = "(! {} {})",
        "_0.as_ref().to_string()",
        "_1.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")"
    )] // ("!" SyGuSBfTerm Attribute+)
    Annotated(Box<SyGuSBfTerm>, Vec<Attribute>),
}

// SyGuSBfTerm = { Identifier | Literal | "(" ~ Identifier ~ SyGuSBfTerm+ ~ ")" | "(" ~ "!" ~ SyGuSBfTerm ~ Attribute+ ~ ")" }
impl SyGuSBfTerm {
    /// Parses a string into a corresponding SyGuS BF term structure.
    /// This function takes an input string, attempts to parse it using the designated syntax rule, and returns a parsed term instance or an error if parsing fails.
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SyGuSBfTerm, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse SyGuSBfTerm: {}", s))
            })?;
        SyGuSBfTerm::parse(pair)
    }
    /// Parses a tokenized syntactic term into its corresponding abstract representation.
    ///
    /// This function takes a parsed pair from the grammar, extracts its inner tokens, and matches them against various expected patterns to construct a valid term.
    /// It distinguishes between simple identifiers or literals and more complex constructs such as applications and annotations, recursively processing nested terms and attributes.
    /// If the input does not match any valid structure, it returns an error detailing the unexpected format.
    ///
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [pair] if pair.as_rule() == Rule::Identifier => Ok(SyGuSBfTerm::Identifier(
                Identifier::from_str(pair.as_str()).unwrap(),
            )),
            [pair] if pair.as_rule() == Rule::Literal => {
                Ok(SyGuSBfTerm::Literal(Literal::from_str(pair.as_str())))
            }
            // Handle Application (Identifier followed by one or more SyGuSBfTerm)
            [id_pair, term_pairs @ ..]
                if id_pair.as_rule() == Rule::Identifier && !term_pairs.is_empty() =>
            {
                let identifier = Identifier::from_str(id_pair.as_str()).unwrap();
                let terms = term_pairs
                    .iter()
                    .map(|p| SyGuSBfTerm::parse(p.clone()))
                    .collect::<Result<Vec<_>, _>>()?;
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

            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Unexpected structure in SyGuSBfTerm parsing: {:?}",
                inner_pairs
            ))),
        }
    }

    pub fn get_name(&self) -> Option<&str> {
        match self {
            SyGuSBfTerm::Identifier(id) => Some(id.get_name()),
            SyGuSBfTerm::Application(id, _) => Some(id.get_name()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Display)]
/// An enumeration representing different forms of a SyGuS grammar term.
/// It distinguishes between a constant with its associated sort, a variable also characterized by a sort, and a base function term utilizing further structural information from SyGuSBfTerm.
///
/// This interface allows users to classify and process SyGuS grammar terms based on their specific syntax and semantics as dictated by the SyGuS v2.1 standard, enabling targeted handling for different term categories during parsing and synthesis.
pub enum SyGuSGTerm {
    #[display(fmt = "{}", _0)] // Sort
    Constant(Sort),
    #[display(fmt = "{}", _0)] // Sort
    Variable(Sort),
    #[display(fmt = "{}", _0)] // SyGuSBfTerm
    SyGuSBfTerm(SyGuSBfTerm),
}

// SyGuSGTerm = { "(" ~ "Constant" ~ Sort ~ ")" | "(" ~ "Variable" ~ Sort ~ ")" | SyGuSBfTerm }
impl SyGuSGTerm {
    /// Parses a string slice into the corresponding abstract syntax tree term following the SyGuS specification.
    ///
    /// This function attempts to convert the input string by first applying the parser to generate an initial parse tree and then processing the parsed result into the desired term format.
    /// On failure to obtain a valid parse tree from the input string, it yields an error indicating invalid syntax.
    ///
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SyGuSGTerm, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse SyGuSGTerm: {}", s))
            })?;
        SyGuSGTerm::parse(pair)
    }
    /// Parses a parse tree node into one of the grammar term variants defined by the SyGuS standard.
    ///
    /// This function processes an input pair, extracting its inner elements and identifying whether it represents a constant, a variable, or a base-form term, then delegates the parsing of associated sorts or subterms as needed.
    /// In case the structure does not match any expected pattern, it returns an error indicating an unexpected syntax structure.
    ///
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
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Unexpected structure in SyGuSGTerm parsing: {:?}",
                inner_pairs
            ))),
        }
    }
}

#[derive(Debug, Clone, Display)]
/// A structure representing a grouped rule list in the SyGuS abstract syntax tree.
/// This layout holds a textual symbol, a sort specification, and a collection of grammar terms generated according to the SyGuS standard.
// GroupedRuleList = { "(" ~ Symbol ~ Sort ~ "(" ~ SyGuSGTerm+ ~ ")" ~ ")" }
#[display(
    fmt = "({} {} ({}))",
    symbol,
    sort,
    "terms.iter().map(|t| t.to_string()).collect::<Vec<_>>().join(\" \")"
)] // (Symbol Sort Vec<SyGuSGTerm>)
pub struct GroupedRuleList {
    pub symbol: Symbol,
    pub sort: Sort,
    pub terms: Vec<SyGuSGTerm>,
}

// GroupedRuleList = { "(" ~ Symbol ~ Sort ~ "(" ~ SyGuSGTerm+ ~ ")" ~ ")" }
impl GroupedRuleList {
    /// Converts a string slice into its corresponding AST representation by parsing the input according to the designated grammar rule.
    ///
    /// Parses the provided string using the SyGuS parser, extracts the first result, and returns a detailed error if the expected structure is absent.
    /// Delegates further interpretation to an internal parsing function, ensuring that any syntax anomalies are appropriately reported through error handling.
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::GroupedRuleList, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse GroupedRuleList: {}", s))
            })?;
        GroupedRuleList::parse(pair)
    }
    /// Parses a syntax tree pair representing a grouped rule list into a corresponding data structure.
    ///
    /// This function consumes an input pair, extracts an identifier as a symbol from the first element, processes the sort from the second element, and then aggregates one or more terms from the remaining pairs, accounting for both direct term references and container forms.
    /// It returns either the constructed grouped rule list or an error if the expected structure is not met.
    ///
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        if inner_pairs.len() >= 2 {
            // Extract symbol (should be the first element)
            let symbol = match inner_pairs.get(0).unwrap() {
                sym_pair => parse_symbol(sym_pair.as_str()).unwrap(),
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
                unreachable!("Expected at least one term in GroupedRuleList, but found none.");
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

#[derive(Debug, Clone, Display)]
/// A structure encapsulating a grammar definition for a SyGuS problem is provided.
///
/// It aggregates sorted variables and grouped rule lists that together specify the grammar's production rules.
///
///
/// The sorted variables field holds a collection of variables with their corresponding sorts, while the grouped rule lists field contains the defined production rules grouped by specific symbols and sorts.
/// This interface organizes essential elements for representing a grammar in the SyGuS v2.1 standard.
// GrammarDef = { ("(" ~ SortedVar+ ~ ")")? ~ "(" ~ GroupedRuleList+ ~ ")" }
#[display(
    fmt = "{}({})",
    "if sorted_vars.is_empty() { String::new() } else { format!(\"({}) \", sorted_vars.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(\" \")) }",
    "grouped_rule_lists.iter().map(|g| g.to_string()).collect::<Vec<_>>().join(\" \")"
)] // (Vec<SortedVar> Vec<GroupedRuleList>)
pub struct GrammarDef {
    pub sorted_vars: Vec<SortedVar>,
    pub grouped_rule_lists: Vec<GroupedRuleList>,
}
impl GrammarDef {
    /// Parses a grammar definition from the provided string slice and returns a corresponding result.
    ///
    ///
    /// Invokes the SyGuS parser to match the grammar definition rule, retrieves the first parsed element, and subsequently delegates further processing to a dedicated parser function.
    /// Returns the successfully parsed grammar definition or an appropriate syntax error if parsing fails.
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::GrammarDef, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse GrammarDef: {}", s))
            })?;
        GrammarDef::parse(pair)
    }
    // GrammarDef = { ("(" ~ SortedVar+ ~ ")")? ~ "(" ~ GroupedRuleList+ ~ ")" }
    /// Parses a pair of tokens into a grammar definition structure.
    ///
    /// This function processes a pest pair representing a grammar definition, extracting sorted variables and grouped rule lists from its inner tokens.
    /// It iterates over each inner element, ensuring that only valid sorted variable or grouped rule list tokens are accepted, and returns a populated grammar definition or an error if unexpected tokens are encountered.
    ///
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
