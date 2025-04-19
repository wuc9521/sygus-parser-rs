use crate::ast::utils::*;
use crate::parser::Rule;
use crate::SyGuSParseError;
use itertools::Itertools;
use pest::iterators::Pair;

// SExpr = { SpecConstant  | Symbol  | Reserved  | Keyword  | "(" ~ SExpr* ~ ")" }
/// Represents an S-expression in the abstract syntax tree of the SyGuS language. 
/// 
/// 
/// Encapsulates different elements that can appear in a SyGuS S-expression by categorizing them into literal specifications, symbols, reserved words, keywords, and nested lists of S-expressions. 
/// This design enables the parser to differentiate among these syntactic forms during the parsing process.
pub enum _SExpr {
    SpecConstant(Literal),
    Symbol(Symbol),
    Reserved(_Reserved),
    Keyword(Identifier),
    List(Vec<_SExpr>),
}

/// Represents reserved lexical elements in SyGuS programs. 
/// 
/// 
/// Encapsulates two kinds of reserved entities: one variant holds a general reserved word as a string, while the other encapsulates a reserved command name corresponding to a specific command.
pub enum _Reserved {
    GeneralWord(String),
    CommandName(_CommandName),
}

impl _Reserved {
    /// Parses a reserved element from a syntactic unit according to the SyGuS standard. 
    /// 
    /// This function attempts to convert a parsed pair into a reserved variant by inspecting the inner pairs of the given syntactic unit. 
    /// It determines whether the unit represents a general word or a command name and returns the corresponding reserved variant. 
    /// In cases where the input does not conform to the expected patterns, it returns an error indicating invalid syntax.
    /// 
    pub fn _parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [id_pair] if id_pair.as_rule() == Rule::Identifier => {
                let identifier = parse_identifier(id_pair.as_str()).unwrap();
                Ok(_Reserved::GeneralWord(identifier))
            }
            [id_pair] if id_pair.as_rule() == Rule::ReservedCommandName => {
                let command_name = _CommandName::_parse(id_pair.clone())?;
                Ok(_Reserved::CommandName(command_name))
            }
            _ => {
                Err(SyGuSParseError::InvalidSyntax(format!(
                    "Expected Reserved, found: {:?}",
                    inner_pairs
                )))
            }
        }
    }
}

/// This enumeration defines the supported command names for processing SyGuS problem inputs. 
/// 
/// 
/// It categorizes a variety of commands used in the SyGuS standard, including those for asserting properties, checking satisfiability, declaring and defining symbols, and interacting with solver options. 
/// Each variant corresponds to a distinct command operation, enabling clear and type-safe handling of the diverse instructions encountered during parsing and processing.
pub enum _CommandName {
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

impl _CommandName {
    /// Parses a pest::iterators::Pair representing a reserved command name into its corresponding command variant. 
    /// 
    /// 
    /// Evaluates the inner pair to match against a predefined set of command name strings defined by the SyGuS specification, returning the associated command enumeration if the input is valid. 
    /// Returns an error indicating invalid syntax if the pair does not conform to the expected rule or contains an unknown command name.
    pub fn _parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner_pairs = pair.into_inner().collect_vec();
        match inner_pairs.as_slice() {
            [id_pair] if id_pair.as_rule() == Rule::ReservedCommandName => {
                let command_name = match id_pair.as_str() {
                    "assert" => _CommandName::Assert,
                    "check-sat" => _CommandName::CheckSat,
                    "check-sat-assuming" => _CommandName::CheckSatAssuming,
                    "declare-const" => _CommandName::DeclareConst,
                    "declare-datatype" => _CommandName::DeclareDatatype,
                    "declare-datatypes" => _CommandName::DeclareDatatypes,
                    "declare-fun" => _CommandName::DeclareFun,
                    "declare-sort" => _CommandName::DeclareSort,
                    "declare-sort-parameter" => _CommandName::DeclareSortParameter,
                    "define-const" => _CommandName::DefineConst,
                    "define-fun" => _CommandName::DefineFun,
                    "define-fun-rec" => _CommandName::DefineFunRec,
                    "define-sort" => _CommandName::DefineSort,
                    "echo" => _CommandName::Echo,
                    "exit" => _CommandName::Exit,
                    "get-assertions" => _CommandName::GetAssertions,
                    "get-assignment" => _CommandName::GetAssignment,
                    "get-info" => _CommandName::GetInfo,
                    "get-model" => _CommandName::GetModel,
                    "get-option" => _CommandName::GetOption,
                    "get-proof" => _CommandName::GetProof,
                    "get-unsat-assumptions" => _CommandName::GetUnsatAssumptions,
                    "get-unsat-core" => _CommandName::GetUnsatCore,
                    "get-value" => _CommandName::GetValue,
                    "pop" => _CommandName::Pop,
                    "push" => _CommandName::Push,
                    "reset" => _CommandName::Reset,
                    "reset-assertions" => _CommandName::ResetAssertions,
                    "set-info" => _CommandName::SetInfo,
                    "set-logic" => _CommandName::SetLogic,
                    "set-option" => _CommandName::SetOption,
                    _ => {
                        return Err(SyGuSParseError::InvalidSyntax(format!(
                            "Unknown command name: {}",
                            id_pair.as_str()
                        )));
                    }
                };
                Ok(command_name)
            }
            _ => {
                Err(SyGuSParseError::InvalidSyntax(format!(
                    "Expected ReservedCommandName, found: {:?}",
                    inner_pairs
                )))
            }
        }
    }
}

// Reserved = { ReservedGeneralWord | ReservedCommandName }
// ReservedGeneralWord = { //
//   "!" | "_" | "as" | "BINARY" | "DECIMAL" | "exists" | "HEXADECIMAL" | "forall" | "let" | "match" | "NUMERAL" | "par" | "STRING"
// }
// ReservedCommandName = {
//   "assert"
// | "check-sat"
// | "check-sat-assuming"
// | "declare-const"
// | "declare-datatype"
// | "declare-datatypes"
// | "declare-fun"
// | "declare-sort"
// | "declare-sort-parameter"
// | "define-const"
// | "define-fun"
// | "define-fun-rec"
// | "define-sort"
// | "echo"
// | "exit"
// | "get-assertions"
// | "get-assignment"
// | "get-info"
// | "get-model"
// | "get-option"
// | "get-proof"
// | "get-unsat-assumptions"
// | "get-unsat-core"
// | "get-value"
// | "pop"
// | "push"
// | "reset"
// | "reset-assertions"
// | "set-info"
// | "set-logic"
// | "set-option"
// }
