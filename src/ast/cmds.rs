use crate::ast::{sorts::*, terms::*, utils::*};
use crate::parser::{Error, Rule, SyGuSParser};
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

#[derive(Debug, Clone)]
pub enum DTConsDecl {
    Constructor(String, Vec<SortedVar>),
}

#[derive(Debug, Clone)]
pub enum DTDecl {
    DataType(Vec<DTConsDecl>),
}

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
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, crate::parser::Error> {
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
                    return Ok(OracleCmd::OracleConstraintIO(symbol, oracle_symbol))
                }
                Rule::SyGuSCmdOracleConstraintCex => {
                    // "(" ~ "oracle-constraint-cex" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintCex(symbol, oracle_symbol))
                }

                Rule::SyGuSCmdOracleConstraintMembership => {
                    // "(" ~ "oracle-constraint-membership" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintMembership(symbol, oracle_symbol))
                }
                Rule::SyGuSCmdOracleConstraintPosWitness => {
                    // "(" ~ "oracle-constraint-poswitness" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintPosWitness(symbol, oracle_symbol))
                }

                Rule::SyGuSCmdOracleConstraintNegWitness => {
                    // "(" ~ "oracle-constraint-negwitness" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::OracleConstraintNegWitness(symbol, oracle_symbol))
                }
                Rule::SyGuSCmdDeclareCorrectnessOracle => {
                    // "(" ~ "declare-correctness-oracle" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::DeclareCorrectnessOracle(symbol, oracle_symbol))
                }
                Rule::SyGuSCmdDeclareCorrectnessCexOracle => {
                    // "(" ~ "declare-correctness-cex-oracle" ~ Symbol{2} ~ ")"
                    let mut inner = pair.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let oracle_symbol = inner.next().unwrap().as_str().to_string();
                    return Ok(OracleCmd::DeclareCorrectnessCexOracle(
                        symbol,
                        oracle_symbol,
                    ))
                }
                _ => unreachable!("Unknown oracle command: {:?}", cmd),
            },
            _ => unreachable!("Unknown oracle command: {:?}", inner),
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
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, crate::parser::Error> {
        let smt_cmd = match pair.as_rule() {
            Rule::DeclareDatatypeCmd => {
                let mut inner = pair.into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let decl = DTDecl::DataType(
                    inner
                        .map(|d| {
                            let mut inner = d.into_inner();
                            DTConsDecl::Constructor(
                                inner.next().unwrap().as_str().to_string(),
                                inner.map(|s| SortedVar::parse(s).unwrap()).collect(),
                            )
                        })
                        .collect(),
                );
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
                        DTDecl::DataType(
                            inner
                                .map(|c| {
                                    let mut inner = c.into_inner();
                                    DTConsDecl::Constructor(
                                        inner.next().unwrap().as_str().to_string(),
                                        inner.map(|s| SortedVar::parse(s).unwrap()).collect(),
                                    )
                                })
                                .collect(),
                        )
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
                        _ => unreachable!("Unknown command: {:?}", inner_cmd),
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
                    Literal::parse(inner.next().unwrap().as_str()),
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
                    Literal::parse(inner.next().unwrap().as_str()),
                )
            }
            _ => unreachable!(),
        };
        Ok(smt_cmd)
    }
}

#[derive(Debug, Clone)]
pub struct SyGuSFile {
    pub cmds: Vec<SyGuSCmd>,
}

impl SyGuSFile {
    pub fn new() -> Self {
        SyGuSFile { cmds: Vec::new() }
    }
    // CheckSynthCmd = { "(" ~ "check-synth" ~ ")" }
    // ChcConstraintCmd = { "(" ~ "chc-constraint" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ SyGuSTerm ~ ")" }
    // ConstraintCmd = { "(" ~ "constraint" ~ SyGuSTerm ~ ")" }
    // DeclareVarCmd = { "(" ~ "declare-var" ~ Symbol ~ Sort ~ ")" }
    // DeclareWeightCmd = { "(" ~ "declare-weight" ~ Symbol ~ Attribute* ~ ")" }
    // InvConstraintCmd = { "(" ~ "inv-constraint" ~ Symbol{4} ~ ")" }
    // OptimizeSynthCmd = { "(" ~ "optimize-synth" ~ "(" ~ SyGuSTerm* ~ ")" ~ Attribute* ~ ")" }
    // SetFeatureCmd = { "(" ~ "set-feature" ~ SyGuSFeature ~ BoolConst ~ ")" }
    // SynthFunCmd = { "(" ~ "synth-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ GrammarDef? ~ ")" }
    pub fn parse(input: &str) -> Result<SyGuSFile, Error> {
        let [file]: [_; 1] = SyGuSParser::parse(Rule::SyGuSProg, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        let mut problem = SyGuSFile::new();
        for cmd in file.into_inner().filter(|c| c.as_rule() != Rule::EOI) {
            let [cmd, ..]: [_; 1] = cmd.into_inner().collect_vec().try_into().unwrap();
            match cmd.as_rule() {
                // SyGuSAssumeCmd = { "(" ~ "assume" ~ SyGuSTerm ~ ")"}
                Rule::SyGuSCmdAssume => {
                    problem.cmds.push(SyGuSCmd::Assume(
                        SyGuSTerm::parse(cmd.into_inner().next().unwrap()).unwrap(),
                    ));
                }
                // SyGuSCheckSynthCmd = { "(" ~ "check-synth" ~ ")" }
                Rule::SyGuSCmdCheckSynth => {
                    problem.cmds.push(SyGuSCmd::CheckSynth);
                }
                // SyGuSChcConstraintCmd = { "(" ~ "chc-constraint" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ SyGuSTerm ~ ")" }
                Rule::SyGuSCmdChcConstraint => {
                    // "(" ~ #SyGuSTkChcConstraint="chc-constraint" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ SyGuSTerm ~ ")"
                    let mut inner = cmd.into_inner();
                    let sorted_vars = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|s| SortedVar::parse(s).unwrap())
                        .collect();
                    let term1 = SyGuSTerm::parse(inner.next().unwrap()).unwrap();
                    let term2 = SyGuSTerm::parse(inner.next().unwrap()).unwrap();
                    problem
                        .cmds
                        .push(SyGuSCmd::ChcConstraint(sorted_vars, term1, term2));
                }
                // SyGuSConstraintCmd = { "(" ~ "constraint" ~ SyGuSTerm ~ ")" }
                Rule::SyGuSCmdConstraint => {
                    // "(" ~ #SyGuSTkConstraint="constraint" ~ SyGuSTerm ~ ")"
                    let inner = cmd.into_inner().next().unwrap();
                    problem
                        .cmds
                        .push(SyGuSCmd::Constraint(SyGuSTerm::parse(inner).unwrap()));
                }
                // SyGuSDeclareVarCmd = { "(" ~ "declare-var" ~ Symbol ~ Sort ~ ")" }
                Rule::SyGuSCmdDeclareVar => {
                    let mut inner = cmd.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    problem.cmds.push(SyGuSCmd::DeclareVar(
                        symbol,
                        Sort::parse(inner.next().unwrap()).unwrap(),
                    ));
                }
                // SyGuSDeclareWeightCmd = { "(" ~ "declare-weight" ~ Symbol ~ Attribute* ~ ")" }
                Rule::SyGuSCmdDeclareWeight => {
                    let mut inner = cmd.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    let attributes = inner.map(|a| Attribute::parse(a).unwrap()).collect_vec();
                    problem
                        .cmds
                        .push(SyGuSCmd::DeclareWeight(symbol, attributes));
                }
                // SyGuSInvConstraintCmd = { "(" ~ "inv-constraint" ~ Symbol{4} ~ ")" }
                Rule::SyGuSCmdInvConstraint => {
                    let mut inner = cmd.into_inner();
                    problem.cmds.push(SyGuSCmd::InvConstraint(
                        inner.next().unwrap().as_str().to_string(),
                        inner.next().unwrap().as_str().to_string(),
                        inner.next().unwrap().as_str().to_string(),
                        inner.next().unwrap().as_str().to_string(),
                    ));
                }
                // SyGuSOptimizeSynthCmd = { "(" ~ "optimize-synth" ~ "(" ~ SyGuSTerm* ~ ")" ~ Attribute* ~ ")" }
                Rule::SyGuSCmdOptimizeSynth => {
                    let mut inner = cmd.into_inner();
                    let terms = inner
                        .next()
                        .unwrap()
                        .into_inner()
                        .map(|t| SyGuSTerm::parse(t).unwrap())
                        .collect_vec();
                    let attributes = inner.map(|a| Attribute::parse(a).unwrap()).collect_vec();
                    problem
                        .cmds
                        .push(SyGuSCmd::OptimizeSynth(terms, attributes));
                }
                // SyGuSSetFeatureCmd = { "(" ~ "set-feature" ~ SyGuSFeature ~ BoolConst ~ ")" }
                Rule::SyGuSCmdSetFeature => {
                    let mut inner = cmd.into_inner();
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
                    problem.cmds.push(SyGuSCmd::SetFeature(feature, value));
                }
                // SyGuSSynthFunCmd = { "(" ~ "synth-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ GrammarDef? ~ ")" }
                Rule::SyGuSCmdSynthFun => {
                    // SynthFunCmd = { "(" ~ "synth-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ GrammarDef? ~ ")" }
                    let mut inner = cmd.into_inner();
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
                            _ => unreachable!("Unknown command: {:?}", inner_cmd),
                        }
                    }
                    problem.cmds.push(SyGuSCmd::SynthFun(
                        symbol,
                        sorted_var_list,
                        ret_sort.unwrap(),
                        grammar_def,
                    ));
                }
                // SyGuSOracleCmd = { "(" ~ "oracle" ~ OracleCmd ~ ")" }
                Rule::SyGuSCmdOracle => {
                    let inner = cmd.into_inner().next().unwrap();
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
                    problem.cmds.push(SyGuSCmd::Oracle(oracle_cmd));
                }
                Rule::SyGuSCmdSMT => {
                    let inner = cmd.into_inner().next().unwrap();
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
                    problem.cmds.push(SyGuSCmd::SMT(smt_cmd));
                }
                _ => {
                    unreachable!("Unknown command: {:?}", cmd)
                }
            }
        }
        Ok(problem)
    }
}
