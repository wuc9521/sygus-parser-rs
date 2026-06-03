use crate::ast::sorts::Sort;
use crate::ast::terms::SyGuSTerm;
use crate::parser::*;
use crate::SyGuSParseError;
use derive_more::Display;
use itertools::Itertools;
use pest::iterators::Pair;

pub type Symbol = String;

#[derive(Debug, Clone, Display, PartialEq, Eq, Hash)]
pub enum Identifier {
    Symbol(Symbol),
    // SMT-LIB indexed-identifier syntax is `(_ <Symbol> <Index>+)`. The
    // leading `_` is part of the syntactic form, not the symbol's name; the
    // parser drops it. Display must put it back for round-trip correctness.
    #[display(
        "(_ {} {})",
        _0,
        _1.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(" ")
    )]
    Indexed(Symbol, Vec<Index>),
}

/// Parses the input string to determine whether it conforms to a valid identifier format according to the SyGuS specification.
///
///
/// Checks first if the string qualifies as a valid symbol; if so, it is returned directly.
/// Otherwise, if the string is enclosed in parentheses, it splits the inner content into parts and validates that there is a proper symbol followed by one or more valid index elements.
/// When these conditions are met, a formatted identifier is returned; otherwise, it yields no result.
impl Identifier {
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [symbol_pair] if symbol_pair.as_rule() == Rule::Symbol => {
                let symbol = parse_symbol(symbol_pair.as_str()).unwrap();
                Ok(Identifier::Symbol(symbol))
            }
            [symbol_pair, index_pairs @ ..] if symbol_pair.as_rule() == Rule::Symbol => {
                let symbol = parse_symbol(symbol_pair.as_str()).unwrap();
                let indices = index_pairs
                    .iter()
                    .map(|pair| Index::from_str(pair.as_str()))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Identifier::Indexed(symbol, indices))
            }
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Expected Identifier, found: {:?}",
                inner_pairs
            ))),
        }
    }
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::Identifier, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse Identifier: {}", s))
            })?;
        Identifier::parse(pair)
    }
    pub fn get_name(&self) -> &str {
        match self {
            Identifier::Symbol(symbol) => symbol,
            Identifier::Indexed(symbol, _) => symbol,
        }
    }

    pub fn to_sexpr(&self) -> SExpr {
        match self {
            Identifier::Symbol(sym) => SExpr::Symbol(sym.clone()),
            Identifier::Indexed(sym, indices) => {
                let mut items = Vec::new();
                items.push(SExpr::Symbol(sym.clone()));
                items.extend(indices.iter().map(|idx| idx.to_sexpr()));
                SExpr::SExprList(items)
            }
        }
    }
}

/// Parses a string slice and determines whether it qualifies as a valid symbol.
///  
/// Validates the input by ensuring it is non-empty and that every character is either an ASCII alphanumeric or one of the allowed special characters, returning the string as a symbol when valid and None otherwise.

// Symbol = @{ (ASCII_ALPHA | SpecialChar) ~ (ASCII_ALPHA | ASCII_DIGIT | SpecialChar)* }
pub fn parse_symbol(s: &str) -> Option<Symbol> {
    if s.is_empty() {
        return None;
    }
    // if s starts with a digit, it is not a symbol
    if s.chars().next().unwrap().is_digit(10) {
        return None;
    }
    // check if all characters are valid
    if s.chars()
        .all(|c| c.is_ascii_alphanumeric() || is_special_char(c))
    {
        return Some(s.to_string());
    }
    None
}

// SpecialChar = @{ "+" | "-" | "/" | "*" | "=" | "%" | "?" | "!" | "." | "$" | "_" | "~" | "&" | "^" | "<" | ">" | "@" }
fn is_special_char(c: char) -> bool {
    matches!(
        c,
        '+' | '-'
            | '/'
            | '*'
            | '='
            | '%'
            | '?'
            | '!'
            | '.'
            | '$'
            | '_'
            | '~'
            | '&'
            | '^'
            | '<'
            | '>'
            | '@'
    )
}

// Numeral = @{"0" | ASCII_NONZERO_DIGIT ~ ASCII_DIGIT*}
#[derive(Debug, Clone, Display, PartialEq, Eq, Hash)]
/// An enumeration representing an index, which defines two distinct variants for numeric and symbolic representations.
///
///
/// It offers a variant to encapsulate an unsigned integer as a numeral index and a variant to encapsulate a string as a symbolic index, facilitating flexible index representations in the parser's abstract syntax tree.
pub enum Index {
    #[display("{}", _0)]
    Numeral(usize),
    #[display("{}", _0)]
    Symbol(String),
}

impl Index {
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::Index, s)?.next().ok_or_else(|| {
            SyGuSParseError::InvalidSyntax(format!("Failed to parse Index: {}", s))
        })?;
        Index::parse(pair)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [numeral_pair] if numeral_pair.as_rule() == Rule::Numeral => {
                let numeral = numeral_pair.as_str().parse::<usize>().unwrap();
                Ok(Index::Numeral(numeral))
            }
            [symbol_pair] if symbol_pair.as_rule() == Rule::Symbol => {
                let symbol = symbol_pair.as_str().to_string();
                Ok(Index::Symbol(symbol))
            }
            _ => Err(SyGuSParseError::InvalidSyntax(format!(
                "Expected Index, found: {:?}",
                inner_pairs
            ))),
        }
    }

    pub fn to_sexpr(&self) -> SExpr {
        match self {
            Index::Numeral(num) => SExpr::SpecConstant(Literal::Numeral(*num)),
            Index::Symbol(sym) => SExpr::Symbol(sym.clone()),
        }
    }
}

// SortedVar = {  "(" ~ Symbol ~ Sort ~ ")"  }
#[derive(Debug, Clone, Display, PartialEq, Eq)]
/// A sorted variable structure encapsulating an identifier and its corresponding type based on the SyGuS specification.
/// It pairs a string-based name with a sort value that defines the variable's type, enabling precise representation of variable declarations within SyGuS problems.
#[display("({name} {sort})")]
pub struct SortedVar {
    pub name: String,
    pub sort: Sort,
}

impl SortedVar {
    /// Parses a string slice into a sorted variable by validating and converting its textual representation according to the expected syntax.
    ///
    ///
    /// Invokes a parser for the sorted variable grammar, retrieves the first matching construct, and then converts the parsed pair into the corresponding structured representation.
    /// In case of failure during parsing or due to syntax mismatches, it returns a detailed error indicating the nature of the parsing issue.
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::SortedVar, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse SortedVar: {}", s))
            })?;
        SortedVar::parse(pair)
    }
    /// Parses a sorted variable from a given parse tree node.
    ///
    /// The function processes a parse pair by extracting its inner pairs and verifying that they match the expected structure.
    ///
    ///
    /// Converts the first inner pair to a variable identifier and uses the sort parser to interpret the second pair as a sort.
    /// If the parse tree node contains exactly two inner pairs as expected, it returns the corresponding sorted variable; otherwise, it produces an error indicating invalid syntax.
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

    pub fn to_sexpr(&self) -> SExpr {
        SExpr::SExprList(vec![SExpr::Symbol(self.name.clone()), self.sort.to_sexpr()])
    }
}

#[derive(Debug, Clone, Display)]
/// A structure representing a variable with a name and an associated sort.
/// It provides a straightforward interface for storing a variable's identifier alongside its designated type sort.
#[display("({name} {sort})")]
pub struct Variable {
    pub name: String,
    pub sort: Sort,
}

#[derive(Debug, Clone, Display, PartialEq)]
/// A variable binding encapsulation that associates an identifier with a SyGuS term.
/// It exposes two fields: a string representing the variable's name and a boxed term that contains the corresponding SyGuS expression, serving as a component within the abstract syntax tree during parsing.
#[display("({name} {})", term)]
pub struct VarBinding {
    pub name: String,
    pub term: Box<SyGuSTerm>,
}

impl VarBinding {
    /// Converts a string representation into a variable binding instance.
    ///
    ///
    /// Attempts to parse the provided string as a variable binding and delegates further parsing to establish its internal structure.
    /// Returns a result containing the constructed instance or an error indicating invalid syntax if the string does not match the expected format.
    pub fn from_str(s: &str) -> Result<Self, SyGuSParseError> {
        let pair = SyGuSParser::parse(Rule::VarBinding, s)?
            .next()
            .ok_or_else(|| {
                SyGuSParseError::InvalidSyntax(format!("Failed to parse VarBinding: {}", s))
            })?;
        VarBinding::parse(pair)
    }
    // VarBinding = { "(" ~ Symbol ~ SyGuSTerm ~ ")" }
    /// Parses a variable binding from a parsed pest pair into a structured instance.
    /// This function accepts a pair from the pest parser representing a variable binding, extracts the symbol and its associated term, and returns a new instance upon successful parsing while delegating errors to the caller.
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

    pub fn to_sexpr(&self) -> SExpr {
        SExpr::SExprList(vec![
            SExpr::Symbol(self.name.to_string()),
            self.term.to_sexpr(),
        ])
    }
}

#[derive(Debug, Clone, Display, PartialEq, PartialOrd)]
/// Represents a literal value parsed from a SyGuS problem, encapsulating various constant forms.
/// This enumeration distinguishes between numeric types, booleans, and textual constants by providing variants for integers, decimals, booleans, hexadecimal constants, binary constants, and string constants.
pub enum Literal {
    #[display("{}", _0)]
    Numeral(usize),
    #[display("{}", _0)]
    Decimal(f64),
    #[display("{}", _0)]
    Bool(bool),
    #[display("#x{}", _0)]
    HexConst(String),
    #[display("#b{}", _0)]
    BinConst(String),
    #[display("{}", _0)]
    StringConst(String),
}

impl Literal {
    /// Converts a string slice into a literal value based on its content.
    ///
    /// Evaluates the provided input by attempting to interpret it as different literal types, starting with a signed integer and then a floating-point number.
    /// It then checks for boolean values, recognizes hexadecimal and binary representations prefixed with "#x" and "#b" respectively, and falls back to treating the input as a string constant if none of the prior cases apply.
    pub fn from_str(s: &str) -> Self {
        if let Ok(num) = s.parse::<usize>() {
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
        if s.starts_with("#x") && s[2..].chars().all(|c| c.is_ascii_hexdigit()) {
            return Literal::HexConst(s[2..].to_string());
        }
        if s.starts_with("#b") && s[2..].chars().all(|c| c == '0' || c == '1') {
            return Literal::BinConst(s[2..].to_string());
        }
        Literal::StringConst(s.to_string())
    }
}

// Attribute = { Keyword  | Keyword ~ AttributeValue }
#[derive(Debug, Clone, Display, PartialEq)]
/// A structure representing an attribute, associating a keyword with an optional value.
/// It encapsulates a string-based keyword that identifies the attribute and an optional value providing additional context or specification, facilitating flexible attribute representation as required by the SyGuS standard.
#[display(
    ":{} {}",
    keyword,
    value.as_ref().map_or(String::new(), |v| v.to_string())
)]
pub struct Attribute {
    pub keyword: String,
    pub value: Option<AttributeValue>,
}

impl Attribute {
    /// Converts a string slice into a parsed attribute, returning either the parsed attribute or a parsing error.
    ///
    ///
    /// Processes a string representing an attribute according to the SyGuS syntax by invoking the parser with the corresponding rule, then hands off the resulting pair to further parsing.
    /// It returns a result type wrapping either the successfully constructed attribute or an error describing the encountered syntax issue.
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
    /// Parses the input pair into an attribute structure by validating that it comprises a single keyword element without an associated value.
    ///
    ///
    /// Checks the inner components of the pair and, if exactly one element matching a keyword is present, creates an attribute instance initialized with that keyword and no additional value.
    /// Otherwise, it returns an error indicating that the syntax does not meet the expected format for an attribute.
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

    pub fn to_sexpr(&self) -> SExpr {
        let mut items = vec![SExpr::Keyword(self.keyword.clone())];
        if let Some(val) = &self.value {
            items.push(val.to_sexpr());
        }
        SExpr::SExprList(items)
    }
}

#[derive(Debug, Clone, Display, PartialEq)]
/// Represents a possible attribute value extracted from a parsed SyGuS problem.
/// It encapsulates three kinds of values: a literal constant specification, a symbolic identifier, or a list of S-expression elements, enabling robust and type-safe handling of attribute values in the abstract syntax tree.
// AttributeValue = { SpecConstant | Symbol | "(" ~ SExpr* ~ ")" }
pub enum AttributeValue {
    SpecConstant(Literal),
    Symbol(String),
    #[display(
        "({})",
        _0.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(" ")
    )]
    SExprList(Vec<SExpr>),
}

impl AttributeValue {
    pub fn to_sexpr(&self) -> SExpr {
        match self {
            AttributeValue::SpecConstant(lit) => SExpr::SpecConstant(lit.clone()),
            AttributeValue::Symbol(sym) => SExpr::Symbol(sym.clone()),
            AttributeValue::SExprList(exprs) => SExpr::SExprList(exprs.clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
/// Enumeration representing a symbolic expression for SyGuS parsing that encapsulates various expression components.
///
///
/// Defines distinct variants to represent a literal constant, a symbol identifier, a reserved string, a keyword, and a nested list of symbolic expressions.
/// This facilitates structured representation of parsed expressions and enables handling of both atomic and compound constructs within the SyGuS language.
pub enum SExpr {
    SpecConstant(Literal),
    Symbol(String),
    Reserved(String),
    Keyword(String),
    SExprList(Vec<SExpr>), //  "(" ~ SExpr* ~ ")"
}

impl From<i64> for SExpr {
    /// Convenience for callers (e.g. delis term lowering) that produce
    /// integer literals; truncates negative values to 0 via `as usize`.
    fn from(n: i64) -> Self {
        SExpr::SpecConstant(Literal::Numeral(n as usize))
    }
}

impl std::fmt::Display for SExpr {
    /// Hand-written so deep trees don't allocate a Vec<String> per node like
    /// derive_more's macro would. The previous version was a measurable
    /// bottleneck (~15% of wall time) when used as the IR for delis bisim.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        match self {
            SExpr::SpecConstant(lit) => write!(f, "{lit}"),
            SExpr::Symbol(s) | SExpr::Reserved(s) | SExpr::Keyword(s) => f.write_str(s),
            SExpr::SExprList(items) => {
                f.write_char('(')?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_char(' ')?;
                    }
                    item.fmt(f)?;
                }
                f.write_char(')')
            }
        }
    }
}

impl SExpr {
    /// Constructs an `SExpr::Symbol` from any string-like input.
    pub fn symbol(s: impl Into<String>) -> Self {
        SExpr::Symbol(s.into())
    }

    /// Constructs an `SExpr::SExprList` from any iterator of children.
    pub fn list<I: IntoIterator<Item = SExpr>>(items: I) -> Self {
        SExpr::SExprList(items.into_iter().collect())
    }

    /// Returns the symbol text if `self` is `Symbol`/`Reserved`/`Keyword`.
    ///
    /// `Reserved` (SMT reserved words like `assert`, `define-fun`) and
    /// `Keyword` (`:foo`) are produced by the pest-driven SyGuS parser but
    /// never by the hand-written `from_str` below; both are exposed here
    /// for callers that walk pre-parsed ASTs.
    ///
    /// `#[inline]` is load-bearing: walk-loops in downstream crates call
    /// this in their hot path; without it the cross-crate boundary costs
    /// 3–4× wall on the delis bisim and encoding paths.
    #[inline]
    pub fn as_symbol(&self) -> Option<&str> {
        match self {
            SExpr::Symbol(s) | SExpr::Reserved(s) | SExpr::Keyword(s) => Some(s.as_str()),
            _ => None,
        }
    }

    /// Returns the integer literal value if `self` is `SpecConstant(Numeral)`.
    #[inline]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            SExpr::SpecConstant(Literal::Numeral(n)) => Some(*n as i64),
            _ => None,
        }
    }

    /// Returns the boolean literal value if `self` is `SpecConstant(Bool)` or
    /// a `Symbol("true"/"false")`. The symbol form arises because most
    /// SyGuS-term-to-SExpr conversions emit booleans as symbols.
    #[inline]
    pub fn as_bool(&self) -> Option<bool> {
        if let SExpr::SpecConstant(Literal::Bool(b)) = self {
            return Some(*b);
        }
        match self.as_symbol()? {
            "true" => Some(true),
            "false" => Some(false),
            _ => None,
        }
    }

    /// Returns the list elements as a borrowed slice without allocating.
    #[inline]
    pub fn as_slice(&self) -> Option<&[SExpr]> {
        match self {
            SExpr::SExprList(items) => Some(items.as_slice()),
            _ => None,
        }
    }

    /// Returns the list elements as `Vec<&SExpr>` (lexpr-compatible API).
    /// Prefer `as_slice` in new code — it doesn't allocate.
    #[inline]
    pub fn to_ref_vec(&self) -> Option<Vec<&SExpr>> {
        match self {
            SExpr::SExprList(items) => Some(items.iter().collect()),
            _ => None,
        }
    }

    /// Hand-written generic s-expression parser. Distinct from the pest-based
    /// SyGuS grammar driver: this accepts any well-balanced s-expression with
    /// atoms classified as integer (`Literal::Numeral`) or symbol. Use it for
    /// parsing fragments embedded inside SyGuS programs (e.g. `define-finite`
    /// record bodies and `define-semantics` match expressions) where the
    /// official SyGuS term grammar is too strict (no zero-arg applications,
    /// no match form, etc.).
    ///
    /// Comments (`;` to end of line) are skipped. Atoms are not interned.
    /// `Reserved` and `Keyword` variants are never produced; SMT reserved
    /// words and `:foo` tokens both come back as `Symbol`.
    pub fn from_str(s: &str) -> Result<Self, SExprParseError> {
        let mut p = SExprParser::new(s);
        p.skip_ws();
        let v = p.parse_one()?;
        p.skip_ws();
        if p.pos < p.bytes.len() {
            return Err(SExprParseError {
                pos: p.pos,
                msg: format!("unexpected trailing input: {:?}", &s[p.pos..]),
            });
        }
        Ok(v)
    }
}

#[derive(Debug)]
pub struct SExprParseError {
    pub pos: usize,
    pub msg: String,
}

impl std::fmt::Display for SExprParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "sexpr parse error at byte {}: {}", self.pos, self.msg)
    }
}

impl std::error::Error for SExprParseError {}

struct SExprParser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> SExprParser<'a> {
    fn new(s: &'a str) -> Self {
        SExprParser {
            bytes: s.as_bytes(),
            pos: 0,
        }
    }

    fn skip_ws(&mut self) {
        loop {
            while self.pos < self.bytes.len() && self.bytes[self.pos].is_ascii_whitespace() {
                self.pos += 1;
            }
            if self.pos < self.bytes.len() && self.bytes[self.pos] == b';' {
                while self.pos < self.bytes.len() && self.bytes[self.pos] != b'\n' {
                    self.pos += 1;
                }
            } else {
                break;
            }
        }
    }

    fn parse_one(&mut self) -> Result<SExpr, SExprParseError> {
        self.skip_ws();
        if self.pos >= self.bytes.len() {
            return Err(SExprParseError {
                pos: self.pos,
                msg: "unexpected end of input".to_string(),
            });
        }
        let c = self.bytes[self.pos];
        if c == b'(' {
            self.pos += 1;
            let mut items = Vec::new();
            loop {
                self.skip_ws();
                if self.pos >= self.bytes.len() {
                    return Err(SExprParseError {
                        pos: self.pos,
                        msg: "unclosed list".to_string(),
                    });
                }
                if self.bytes[self.pos] == b')' {
                    self.pos += 1;
                    return Ok(SExpr::SExprList(items));
                }
                items.push(self.parse_one()?);
            }
        }
        if c == b')' {
            return Err(SExprParseError {
                pos: self.pos,
                msg: "unexpected )".to_string(),
            });
        }
        let start = self.pos;
        while self.pos < self.bytes.len() {
            let b = self.bytes[self.pos];
            if b.is_ascii_whitespace() || b == b'(' || b == b')' || b == b';' {
                break;
            }
            self.pos += 1;
        }
        let atom = std::str::from_utf8(&self.bytes[start..self.pos]).map_err(|e| {
            SExprParseError {
                pos: start,
                msg: e.to_string(),
            }
        })?;
        if let Ok(n) = atom.parse::<usize>() {
            return Ok(SExpr::SpecConstant(Literal::Numeral(n)));
        }
        Ok(SExpr::Symbol(atom.to_string()))
    }
}

#[cfg(test)]
mod sexpr_tests {
    use super::*;

    #[test]
    fn parses_atoms() {
        assert_eq!(
            SExpr::from_str("foo").unwrap(),
            SExpr::Symbol("foo".into())
        );
        assert_eq!(
            SExpr::from_str("42").unwrap(),
            SExpr::SpecConstant(Literal::Numeral(42))
        );
        assert_eq!(SExpr::from_str("true").unwrap().as_bool(), Some(true));
        assert_eq!(SExpr::from_str("false").unwrap().as_bool(), Some(false));
    }

    #[test]
    fn parses_empty_and_singleton_lists() {
        assert_eq!(SExpr::from_str("()").unwrap(), SExpr::SExprList(vec![]));
        assert_eq!(
            SExpr::from_str("(ltl.p0)").unwrap(),
            SExpr::SExprList(vec![SExpr::Symbol("ltl.p0".into())])
        );
    }

    #[test]
    fn parses_nested() {
        let v = SExpr::from_str("(and (= a b) (not c))").unwrap();
        let list = v.as_slice().unwrap();
        assert_eq!(list[0].as_symbol(), Some("and"));
        assert_eq!(list.len(), 3);
    }

    #[test]
    fn handles_comments() {
        let v = SExpr::from_str("(a ; comment\n b)").unwrap();
        assert_eq!(v.as_slice().unwrap().len(), 2);
    }

    #[test]
    fn round_trips_via_display() {
        let src = "(match phi ((ltl.p0) (p0 (t asp))) ((ltl.not x) (not (LTL.Sem x asp))))";
        let v = SExpr::from_str(src).unwrap();
        let s = v.to_string();
        let v2 = SExpr::from_str(&s).unwrap();
        assert_eq!(v, v2);
    }

    #[test]
    fn parses_symbols_with_special_chars() {
        let v = SExpr::from_str("($neg1 + next.depth)").unwrap();
        let list = v.as_slice().unwrap();
        assert_eq!(list[0].as_symbol(), Some("$neg1"));
        assert_eq!(list[1].as_symbol(), Some("+"));
        assert_eq!(list[2].as_symbol(), Some("next.depth"));
    }

    #[test]
    fn rejects_trailing_garbage() {
        assert!(SExpr::from_str("(a) extra").is_err());
    }
}

#[derive(Debug, Clone, Display)]
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
