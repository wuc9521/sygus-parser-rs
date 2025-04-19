use crate::ast::sorts::Sort;
use crate::ast::terms::SyGuSTerm;
use crate::parser::*;
use crate::SyGuSParseError;
use itertools::Itertools;
use pest::iterators::Pair;

pub type Identifier = String;
pub type Symbol = String;

// Identifier = {   Symbol   | "(" ~ "_"? ~ Symbol ~ Index+ ~ ")"
// Symbol = @{ (ASCII_ALPHA | SpecialChar) ~ (ASCII_ALPHA | ASCII_DIGIT | SpecialChar)* }
// SpecialChar = @{ "+" | "-" | "/" | "*" | "=" | "%" | "?" | "!" | "." | "$" | "_" | "~" | "&" | "^" | "<" | ">" | "@" }
// Index = {  Numeral  | Symbol  }

pub fn parse_identifier(s: &str) -> Option<Identifier> {
    if parse_symbol(s).is_some() {
        return Some(s.to_string());
    }
    if s.starts_with('(') && s.ends_with(')') {
        let inner = &s[1..s.len() - 1];
        if inner.is_empty() {
            return None;
        }
        let parts: Vec<&str> = inner.split_whitespace().collect();
        if parts.len() < 2 {
            return None;
        }
        let symbol = parts[0].to_string();
        let indices: Vec<String> = parts[1..]
            .iter()
            .filter_map(|&index| parse_symbol(index))
            .collect();
        if indices.is_empty() {
            return None;
        }
        return Some(format!("({} {})", symbol, indices.join(" ")));
    }
    None
}

pub fn parse_symbol(s: &str) -> Option<Symbol> {
    if s.is_empty() {
        return None;
    }
    if s.chars()
        .all(|c| c.is_ascii_alphanumeric() || "+-*/=?!.@$~&^<>".contains(c))
    {
        return Some(s.to_string());
    }
    None
}

// Numeral = @{"0" | ASCII_NONZERO_DIGIT ~ ASCII_DIGIT*}
#[derive(Debug, Clone)]
pub enum Index {
    Numeral(usize),
    Symbol(String),
}

#[derive(Debug, Clone)]
pub struct SortedVar {
    pub name: String,
    pub sort: Sort,
}

impl SortedVar {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SortedVar, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse SortedVar: {}", s))
            })?;
        SortedVar::parse(pair)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [symbol_pair, sort_pair] => {
                let symbol = symbol_pair.as_str().to_string();
                let sort = Sort::parse(sort_pair.clone())?;
                Ok(SortedVar { name: symbol, sort })
            }
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Expected SortedVar, found: {:?}",
                inner_pairs
            ))),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub sort: Sort,
}

#[derive(Debug, Clone)]
pub struct VarBinding {
    pub name: String,
    pub term: Box<SyGuSTerm>,
}

impl VarBinding {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::VarBinding, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse VarBinding: {}", s))
            })?;
        VarBinding::parse(pair)
    }
    // VarBinding = { "(" ~ Symbol ~ SyGuSTerm ~ ")" }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [symbol_pair, term_pair] => {
                let symbol = symbol_pair.as_str().to_string();
                let term = SyGuSTerm::parse(term_pair.clone())?;
                Ok(VarBinding {
                    name: symbol,
                    term: Box::new(term),
                })
            }
            _ => unimplemented!(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Numeral(i64),
    Decimal(f64),
    Bool(bool),
    HexConst(String),
    BinConst(String),
    StringConst(String),
}

impl Literal {
    pub fn from_str(s: &str) -> Self {
        if let Ok(num) = s.parse::<i64>() {
            return Literal::Numeral(num);
        }
        if let Ok(num) = s.parse::<f64>() {
            return Literal::Decimal(num);
        }
        if s == "true" {
            return Literal::Bool(true);
        }
        if s == "false" {
            return Literal::Bool(false);
        }
        if s.starts_with("#x") && s[2..].chars().all(|c| c.is_digit(16)) {
            return Literal::HexConst(s.to_string());
        }
        if s.starts_with("#b") && s[2..].chars().all(|c| c == '0' || c == '1') {
            return Literal::BinConst(s.to_string());
        }
        Literal::StringConst(s.to_string())
    }
}

// Attribute = { Keyword  | Keyword ~ AttributeValue }
#[derive(Debug, Clone)]
pub struct Attribute {
    pub keyword: String,
    pub value: Option<AttributeValue>,
}

impl Attribute {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::Attribute, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse Attribute: {}", s))
            })?;
        Attribute::parse(pair)
    }
    // AttributeValue = { SpecConstant | Symbol | "(" ~ SExpr* ~ ")" }
    // SExpr = { // borrowed from SMT-lib
    // SpecConstant  | Symbol | Reserved  | Keyword  | "(" ~ SExpr* ~ ")" }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [keyword_pair] if keyword_pair.as_rule() == Rule::Keyword => {
                let keyword = keyword_pair.as_str().to_string();
                Ok(Attribute {
                    keyword,
                    value: None,
                })
            }
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Expected Attribute, found: {:?}",
                inner_pairs
            ))),
        }
    }
}

#[derive(Debug, Clone)]
pub enum AttributeValue {
    SpecConstant(Literal),
    Symbol(String),
    SExprList(Vec<SExpr>),
}

#[derive(Debug, Clone)]
pub enum SExpr {
    SpecConstant(Literal),
    Symbol(String),
    Reserved(String),
    Keyword(String),
    SExprList(Vec<SExpr>),
}

pub enum ReservedCommand {
    Assert,
    CheckSat,
    CheckSatAssuming,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DeclareSort,
    DeclareSortParameter,
    DefineConst,
    DefineFun,
    DefineFunRec,
    DefineSort,
    Echo,
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Reset,
    ResetAssertions,
    SetInfo,
    SetLogic,
    SetOption,
}

impl ReservedCommand {
    pub fn from_str(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [id_pair] if id_pair.as_rule() == Rule::ReservedCommandName => {
                let command_name = match id_pair.as_str() {
                    "assert" => ReservedCommand::Assert,
                    "check-sat" => ReservedCommand::CheckSat,
                    "check-sat-assuming" => ReservedCommand::CheckSatAssuming,
                    "declare-const" => ReservedCommand::DeclareConst,
                    "declare-datatype" => ReservedCommand::DeclareDatatype,
                    "declare-datatypes" => ReservedCommand::DeclareDatatypes,
                    "declare-fun" => ReservedCommand::DeclareFun,
                    "declare-sort" => ReservedCommand::DeclareSort,
                    "declare-sort-parameter" => ReservedCommand::DeclareSortParameter,
                    "define-const" => ReservedCommand::DefineConst,
                    "define-fun" => ReservedCommand::DefineFun,
                    "define-fun-rec" => ReservedCommand::DefineFunRec,
                    "define-sort" => ReservedCommand::DefineSort,
                    "echo" => ReservedCommand::Echo,
                    "exit" => ReservedCommand::Exit,
                    "get-assertions" => ReservedCommand::GetAssertions,
                    "get-assignment" => ReservedCommand::GetAssignment,
                    "get-info" => ReservedCommand::GetInfo,
                    "get-model" => ReservedCommand::GetModel,
                    "get-option" => ReservedCommand::GetOption,
                    "get-proof" => ReservedCommand::GetProof,
                    "get-unsat-assumptions" => ReservedCommand::GetUnsatAssumptions,
                    "get-unsat-core" => ReservedCommand::GetUnsatCore,
                    "get-value" => ReservedCommand::GetValue,
                    "pop" => ReservedCommand::Pop,
                    "push" => ReservedCommand::Push,
                    "reset" => ReservedCommand::Reset,
                    "reset-assertions" => ReservedCommand::ResetAssertions,
                    "set-info" => ReservedCommand::SetInfo,
                    "set-logic" => ReservedCommand::SetLogic,
                    "set-option" => ReservedCommand::SetOption,
                    _ => {
                        return Err(SyGuSParseError::InvalidSyntax(format!(
                            "Unknown command name: {}",
                            id_pair.as_str()
                        )));
                    }
                };
                Ok(command_name)
            }
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Expected ReservedCommandName, found: {:?}",
                inner_pairs
            ))),
        }
    }
}
