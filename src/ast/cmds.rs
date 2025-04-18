use crate::ast::{sorts::*, terms::*, utils::*};
use crate::parser::{Rule, SyGuSParser};
use crate::SyGuSParseError;
use core::fmt;
use itertools::Itertools;
use pest::iterators::Pair;
use pest::Parser; // important for ::parse method.

#[derive(Debug, Clone)]
pub enum SyGuSFeature {
    Grammars,
    FwdDecls,
    Recursion,
    Oracles,
    Weights,
}

type DTConsDecl = (String, Vec<SortedVar>);
type DTDecl = Vec<DTConsDecl>;

#[derive(Debug, Clone)]
pub struct SortDecl {
    pub symbol: String,
    pub arity: usize,
}

#[derive(Debug, Clone)]
pub enum SyGuSCmd {
    Assume(SyGuSTerm),
    CheckSynth,
    ChcConstraint(Vec<SortedVar>, SyGuSTerm, SyGuSTerm),
    Constraint(SyGuSTerm),
    DeclareVar(String, Sort),
    DeclareWeight(String, Vec<Attribute>),
    InvConstraint(String, String, String, String),
    OptimizeSynth(Vec<SyGuSTerm>, Vec<Attribute>),
    SetFeature(SyGuSFeature, bool),
    SetLogic(String),
    SynthFun(String, Vec<SortedVar>, Sort, Option<GrammarDef>),
    Oracle(OracleCmd),
    SMT(SMTCmd),
}

#[derive(Debug, Clone)]
pub enum OracleCmd {
    OracleAssume(Vec<SortedVar>, Vec<SortedVar>, SyGuSTerm, String),
    OracleConstraint(Vec<SortedVar>, Vec<SortedVar>, SyGuSTerm, String),
    DeclareOracleFun(String, Vec<Sort>, Sort, String),
    OracleConstraintIO(String, String),
    OracleConstraintCex(String, String),
    OracleConstraintMembership(String, String),
    OracleConstraintPosWitness(String, String),
    OracleConstraintNegWitness(String, String),
    DeclareCorrectnessOracle(String, String),
    DeclareCorrectnessCexOracle(String, String),
}

impl OracleCmd {
    pub fn from_str(input: &str) -> Result<OracleCmd, SyGuSParseError> {
        let [cmd]: [_; 1] = SyGuSParser::parse(Rule::SyGuSCmdOracle, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        OracleCmd::parse(cmd)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let inner = pair.clone().into_inner().collect_vec();
        match inner.as_slice() {
            [cmd, ..] => match cmd.as_rule() {
                Rule::SyGuSCmdOracleAssume => {
                    // "(" ~ "oracle-assume" ~ "(" ~ SortedVar* ~ ")" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ Symbol ~ ")"
                    let mut inner = pair.into_inner();
                    let sorted_vars = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|s| SortedVar::parse(s).unwrap())
                        .collect();
                    let sorted_vars2 = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|s| SortedVar::parse(s).unwrap())
                        .collect();
                    let term = SyGuSTerm::parse(inner.next().unwrap()).unwrap();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleAssume(
                        sorted_vars,
                        sorted_vars2,
                        term,
                        symbol,
                    ));
                }
                Rule::SyGuSCmdConstraint => {
                    // "(" ~ "oracle-constraint" ~ "(" ~ SortedVar* ~ ")" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ Symbol ~ ")"
                    let mut inner = pair.into_inner();
                    let sorted_vars = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|s| SortedVar::parse(s).unwrap())
                        .collect();
                    let sorted_vars2 = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|s| SortedVar::parse(s).unwrap())
                        .collect();
                    let term = SyGuSTerm::parse(inner.next().unwrap()).unwrap();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraint(
                        sorted_vars,
                        sorted_vars2,
                        term,
                        symbol,
                    ));
                }
                Rule::SyGuSCmdDeclareOracleFun => {
                    // "(" ~ "declare-oracle-fun" ~ Symbol ~ "(" ~ Sort* ~ ")" ~ Sort ~ Symbol ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let sorts = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|s| Sort::parse(s).unwrap())
                        .collect_vec();
                    let ret_sort = Sort::parse(inner.next().unwrap()).unwrap();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::DeclareOracleFun(
                        symbol,
                        sorts,
                        ret_sort,
                        oracle_symbol,
                    ));
                }
                Rule::SyGuSCmdOracleConstraintIO => {
                    // "(" ~ "oracle-constraint-io" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintIO(symbol, oracle_symbol));
                }
                Rule::SyGuSCmdOracleConstraintCex => {
                    // "(" ~ "oracle-constraint-cex" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintCex(symbol, oracle_symbol));
                }

                Rule::SyGuSCmdOracleConstraintMembership => {
                    // "(" ~ "oracle-constraint-membership" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintMembership(symbol, oracle_symbol));
                }
                Rule::SyGuSCmdOracleConstraintPosWitness => {
                    // "(" ~ "oracle-constraint-poswitness" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintPosWitness(symbol, oracle_symbol));
                }

                Rule::SyGuSCmdOracleConstraintNegWitness => {
                    // "(" ~ "oracle-constraint-negwitness" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintNegWitness(symbol, oracle_symbol));
                }
                Rule::SyGuSCmdDeclareCorrectnessOracle => {
                    // "(" ~ "declare-correctness-oracle" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::DeclareCorrectnessOracle(symbol, oracle_symbol));
                }
                Rule::SyGuSCmdDeclareCorrectnessCexOracle => {
                    // "(" ~ "declare-correctness-cex-oracle" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::DeclareCorrectnessCexOracle(
                        symbol,
                        oracle_symbol,
                    ));
                }
                _ => {
                    return Err(SyGuSParseError::InvalidSyntax(format!(
                        "Unknown oracle command: {:?}",
                        cmd.as_rule()
                    )))
                }
            },
            _ => {
                return Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unknown oracle command: {:?}",
                    pair.as_rule()
                )))
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum SMTCmd {
    DeclareDatatype(String, DTDecl),
    DeclareDatatypes(Vec<SortDecl>, Vec<DTDecl>),
    DeclareSort(String, usize),
    DefineFun(String, Vec<SortedVar>, Sort, SyGuSTerm),
    DefineSort(String, Sort),
    SetInfo(String, Literal),
    SetLogic(String),
    SetOption(String, Literal),
}

impl SMTCmd {
    pub fn from_str(input: &str) -> Result<SMTCmd, SyGuSParseError> {
        let [cmd]: [_; 1] = SyGuSParser::parse(Rule::SyGuSCmdSMT, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        SMTCmd::parse(cmd)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        let smt_cmd = match pair.as_rule() {
            Rule::DeclareDatatypeCmd => {
                let mut inner = pair.into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let decl = inner
                    .map(|d| {
                        let mut inner = d.into_inner();
                        (
                            inner.next().unwrap().as_str().to_string(),
                            inner.map(|s| SortedVar::parse(s).unwrap()).collect(),
                        )
                    })
                    .collect();
                SMTCmd::DeclareDatatype(symbol, decl)
            }
            // "(" ~ "declare-datatype" ~ Symbol ~ DTDecl ~ ")"
            // DTDecl = { "(" ~ DTConsDecl+ ~ ")" }
            // DTConsDecl = { "(" ~ Symbol ~ SortedVar* ~ ")" }
            Rule::DeclareDatatypesCmd => {
                let mut inner = pair.into_inner();
                let sorts = inner
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|s| SortDecl {
                        symbol: s.as_str().to_string(),
                        arity: s.as_str().len(),
                    })
                    .collect();
                let decls = inner
                    .map(|d| {
                        let inner = d.into_inner();
                        inner
                            .map(|c| {
                                let mut inner = c.into_inner();
                                (
                                    inner.next().unwrap().as_str().to_string(),
                                    inner.map(|s| SortedVar::parse(s).unwrap()).collect(),
                                )
                            })
                            .collect()
                    })
                    .collect();
                SMTCmd::DeclareDatatypes(sorts, decls)
            }
            Rule::DeclareSortCmd => {
                let mut inner = pair.into_inner();
                SMTCmd::DeclareSort(
                    inner.next().unwrap().as_str().to_string(),
                    inner.next().unwrap().as_str().parse::<usize>().unwrap(),
                )
            }
            Rule::DefineFunCmd => {
                // DefineFunCmd = { "(" ~ "define-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ SyGuSTerm ~ ")" }
                let mut inner = pair.into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let mut sorted_var_list = Vec::new();
                let mut ret_sort = None;
                let mut term = None;
                for inner_cmd in inner {
                    match inner_cmd.as_rule() {
                        Rule::SortedVar => {
                            // let sorted_var = SortedVar::parse(inner_cmd);
                            sorted_var_list.push(SortedVar::parse(inner_cmd).unwrap());
                        }
                        Rule::Sort => {
                            ret_sort = Some(Sort::parse(inner_cmd).unwrap());
                        }
                        Rule::SyGuSTerm => {
                            term = Some(SyGuSTerm::parse(inner_cmd).unwrap());
                        }
                        _ => {
                            return Err(SyGuSParseError::InvalidSyntax(format!(
                                "Unknown define-fun command: {:?}",
                                inner_cmd
                            )))
                        }
                    }
                }
                SMTCmd::DefineFun(symbol, sorted_var_list, ret_sort.unwrap(), term.unwrap())
            }
            Rule::DefineSortCmd => {
                let mut inner = pair.into_inner();
                let sort = Sort::parse(inner.next().unwrap()).unwrap();
                SMTCmd::DefineSort(inner.next().unwrap().as_str().to_string(), sort)
            }
            Rule::SetInfoCmd => {
                let mut inner = pair.into_inner();
                SMTCmd::SetInfo(
                    inner.next().unwrap().as_str().to_string(),
                    Literal::from_str(inner.next().unwrap().as_str()),
                )
            }
            Rule::SetLogicCmd => {
                let mut inner = pair.into_inner();
                SMTCmd::SetLogic(inner.next().unwrap().as_str().to_string())
            }
            Rule::SetOptionCmd => {
                let mut inner = pair.into_inner();
                SMTCmd::SetOption(
                    inner.next().unwrap().as_str().to_string(),
                    Literal::from_str(inner.next().unwrap().as_str()),
                )
            }
            _ => {
                return Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unknown SMT command: {:?}",
                    pair.as_rule()
                )))
            }
        };
        Ok(smt_cmd)
    }
}

#[derive(Debug, Clone)]
pub struct SyGuSFile {
    pub cmds: Vec<SyGuSCmd>,
}

impl fmt::Display for SyGuSFile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for cmd in &self.cmds {
            write!(f, "{:?}\n", cmd)?;
        }
        Ok(())
    }
}

impl SyGuSFile {
    pub fn new() -> Self {
        SyGuSFile { cmds: Vec::new() }
    }
    pub fn from_str(input: &str) -> Result<SyGuSFile, SyGuSParseError> {
        let [file]: [_; 1] = SyGuSParser::parse(Rule::SyGuSProg, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        let mut problem = SyGuSFile::new();
        for cmd in file.into_inner().filter(|c| c.as_rule() != Rule::EOI) {
            let [cmd, ..]: [_; 1] = cmd.into_inner().collect_vec().try_into().unwrap();
            problem.cmds.push(SyGuSCmd::parse(cmd.clone()).unwrap());
        }
        Ok(problem)
    }
}

impl SyGuSCmd {
    pub fn from_str(input: &str) -> Result<SyGuSCmd, SyGuSParseError> {
        let [cmd]: [_; 1] = SyGuSParser::parse(Rule::SyGuSCmd, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        SyGuSCmd::parse(cmd)
    }
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
        println!("SyGuSCmd: {:?}", pair);
        match pair.as_rule() {
            Rule::SyGuSCmd => {
                // into next level
                let inner = pair.clone().into_inner().next().unwrap();
                return SyGuSCmd::parse(inner);
            }
            Rule::SyGuSCmdAssume => {
                // SyGuSAssumeCmd = { "(" ~ "assume" ~ SyGuSTerm ~ ")"}
                let term = SyGuSTerm::parse(pair.into_inner().next().unwrap()).unwrap();
                return Ok(SyGuSCmd::Assume(term));
            }
            Rule::SyGuSCmdCheckSynth => {
                // "(" ~ "check-synth" ~ ")"
                return Ok(SyGuSCmd::CheckSynth);
            }
            Rule::SyGuSCmdChcConstraint => {
                // "(" ~ #SyGuSTkChcConstraint="chc-constraint" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ SyGuSTerm ~ ")"
                let mut inner = pair.clone().into_inner();
                let sorted_vars = inner
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|s| SortedVar::parse(s).unwrap())
                    .collect();
                let term1 = SyGuSTerm::parse(inner.next().unwrap()).unwrap();
                let term2 = SyGuSTerm::parse(inner.next().unwrap()).unwrap();
                return Ok(SyGuSCmd::ChcConstraint(sorted_vars, term1, term2));
            }
            Rule::SyGuSCmdConstraint => {
                // "(" ~ #SyGuSTkConstraint="constraint" ~ SyGuSTerm ~ ")"
                let inner = pair.clone().into_inner().next().unwrap();
                return Ok(SyGuSCmd::Constraint(SyGuSTerm::parse(inner).unwrap()));
            }
            Rule::SyGuSCmdDeclareVar => {
                // "(" ~ "declare-var" ~ Symbol ~ Sort ~ ")"
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::DeclareVar(
                    symbol,
                    Sort::parse(inner.next().unwrap()).unwrap(),
                ));
            }
            Rule::SyGuSCmdDeclareWeight => {
                // "(" ~ "declare-weight" ~ Symbol ~ Attribute* ~ ")"
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let attributes = inner.map(|a| Attribute::parse(a).unwrap()).collect_vec();
                return Ok(SyGuSCmd::DeclareWeight(symbol, attributes));
            }

            Rule::SyGuSCmdInvConstraint => {
                // SyGuSInvConstraintCmd = { "(" ~ "inv-constraint" ~ Symbol{4} ~ ")" }
                let mut inner = pair.clone().into_inner();
                return Ok(SyGuSCmd::InvConstraint(
                    inner.next().unwrap().as_str().to_string(),
                    inner.next().unwrap().as_str().to_string(),
                    inner.next().unwrap().as_str().to_string(),
                    inner.next().unwrap().as_str().to_string(),
                ));
            }
            // SyGuSOptimizeSynthCmd = { "(" ~ "optimize-synth" ~ "(" ~ SyGuSTerm* ~ ")" ~ Attribute* ~ ")" }
            Rule::SyGuSCmdOptimizeSynth => {
                // "(" ~ "optimize-synth" ~ "(" ~ SyGuSTerm* ~ ")" ~ Attribute* ~ ")"
                let mut inner = pair.clone().into_inner();
                let terms = inner
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|t| SyGuSTerm::parse(t).unwrap())
                    .collect_vec();
                let attributes = inner.map(|a| Attribute::parse(a).unwrap()).collect_vec();
                return Ok(SyGuSCmd::OptimizeSynth(terms, attributes));
            }
            Rule::SyGuSCmdSetFeature => {
                // "(" ~ "set-feature" ~ Symbol{2} ~ BoolConst ~ ")"
                let mut inner = pair.clone().into_inner();
                let feature = inner.next().unwrap().as_str().to_string();
                let value = inner.next().unwrap().as_str().to_string();
                let feature = match feature.as_str() {
                    "grammars" => SyGuSFeature::Grammars,
                    "fwd-decls" => SyGuSFeature::FwdDecls,
                    "recursion" => SyGuSFeature::Recursion,
                    "oracles" => SyGuSFeature::Oracles,
                    "weights" => SyGuSFeature::Weights,
                    _ => panic!("Unknown feature: {}", feature),
                };
                let value = value.parse::<bool>().unwrap();
                return Ok(SyGuSCmd::SetFeature(feature, value));
            }
            Rule::SyGuSCmdSynthFun => {
                // SynthFunCmd = { "(" ~ "synth-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ GrammarDef? ~ ")" }
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let mut sorted_var_list = Vec::new();
                let mut ret_sort = None;
                let mut grammar_def = None;
                for inner_cmd in inner {
                    match inner_cmd.as_rule() {
                        Rule::SortedVar => {
                            // let sorted_var = SortedVar::parse(inner_cmd);
                            sorted_var_list.push(SortedVar::parse(inner_cmd).unwrap());
                        }
                        Rule::Sort => {
                            ret_sort = Some(Sort::parse(inner_cmd).unwrap());
                        }
                        Rule::GrammarDef => {
                            grammar_def = Some(GrammarDef::parse(inner_cmd).unwrap());
                        }
                        _ => {
                            return Err(SyGuSParseError::InvalidSyntax(format!(
                                "Unknown synth-fun command: {:?}",
                                inner_cmd
                            )))
                        }
                    }
                }
                return Ok(SyGuSCmd::SynthFun(
                    symbol,
                    sorted_var_list,
                    ret_sort.unwrap(),
                    grammar_def,
                ));
            }
            // SyGuSOracleCmd = { "(" ~ "oracle" ~ OracleCmd ~ ")" }
            Rule::SyGuSCmdOracle => {
                let inner = pair.clone().into_inner().next().unwrap();
                let oracle_cmd = OracleCmd::parse(inner).unwrap();
                match oracle_cmd.clone() {
                    OracleCmd::OracleAssume(_, _, _, _) => {}
                    OracleCmd::OracleConstraint(_, _, _, _) => {}
                    OracleCmd::DeclareOracleFun(_, _, _, _) => {}
                    OracleCmd::OracleConstraintIO(_, _) => {}
                    OracleCmd::OracleConstraintCex(_, _) => {}
                    OracleCmd::OracleConstraintMembership(_, _) => {}
                    OracleCmd::OracleConstraintPosWitness(_, _) => {}
                    OracleCmd::OracleConstraintNegWitness(_, _) => {}
                    OracleCmd::DeclareCorrectnessOracle(_, _) => {}
                    OracleCmd::DeclareCorrectnessCexOracle(_, _) => {}
                }
                return Ok(SyGuSCmd::Oracle(oracle_cmd));
            }
            Rule::SyGuSCmdSMT => {
                let inner = pair.clone().into_inner().next().unwrap();
                let smt_cmd = SMTCmd::parse(inner).unwrap();
                match smt_cmd.clone() {
                    SMTCmd::DeclareDatatype(_, _) => {}
                    SMTCmd::DeclareDatatypes(_, _) => {}
                    SMTCmd::DeclareSort(_, _) => {}
                    SMTCmd::DefineFun(_, _, _, _) => {}
                    SMTCmd::DefineSort(_, _) => {}
                    SMTCmd::SetInfo(_, _) => {}
                    SMTCmd::SetLogic(_) => {}
                    SMTCmd::SetOption(_, _) => {}
                }
                return Ok(SyGuSCmd::SMT(smt_cmd));
            }
            _ => {
                println!("Unknown command: {:?}\n{:?}", pair.as_rule(), pair.as_str());
                return Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unknown command: {:?}",
                    pair.as_rule()
                )))
            }
        }
    }
}
