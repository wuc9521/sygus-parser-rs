use crate::ast::utils::*;
use crate::parser::Rule;
use crate::SyGuSParseError;
use itertools::Itertools;
use pest::iterators::Pair;

// SExpr = { SpecConstant  | Symbol  | Reserved  | Keyword  | "(" ~ SExpr* ~ ")" }
pub enum _SExpr {
    SpecConstant(Literal),
    Symbol(Symbol),
    Reserved(_Reserved),
    Keyword(Identifier),
    List(Vec<_SExpr>),
}

pub enum _Reserved {
    GeneralWord(String),
    CommandName(_CommandName),
}

impl _Reserved {
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
