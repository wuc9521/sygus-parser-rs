use crate::ast::{common::*, sorts::*, terms::*};
use crate::parser::{Error, Rule, SyGuSParser};
use itertools::Itertools;
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

#[derive(Debug, Clone)]
pub struct SyGuSProblem {
    pub logic: Option<String>,
    pub variables: Vec<Variable>,
    pub constraints: Vec<SyGuSTerm>,
    pub synthfuns: Vec<SynthFun>,
    pub cmds: Vec<SyGuSCmd>,
}

#[derive(Debug, Clone)]
pub struct SynthFun {
    pub name: String,
    pub sorted_vars: Vec<SortedVar>,
    pub return_sort: Sort,
    pub grammar_def: Option<GrammarDef>,
}

impl SyGuSProblem {
    pub fn new() -> Self {
        SyGuSProblem {
            logic: None,
            variables: Vec::new(),
            constraints: Vec::new(),
            synthfuns: Vec::new(),
            cmds: Vec::new(),
        }
    }
    pub fn parse(input: &str) -> Result<SyGuSProblem, Error> {
        let [file]: [_; 1] = SyGuSParser::parse(Rule::SyGuSProg, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        let mut problem = SyGuSProblem::new();
        for cmd in file.into_inner().filter(|c| c.as_rule() != Rule::EOI) {
            let cmd = cmd.into_inner().next().unwrap();
            match cmd.as_rule() {
                Rule::AssumeCmd => {
                    unimplemented!();
                    // let inner = cmd.into_inner().next().unwrap();
                    // let term = SyGuSTerm::parse(inner.as_str());
                    // problem.cmds.push(SyGuSCmd::Assume(term));
                }
                Rule::CheckSynthCmd => {
                    problem.cmds.push(SyGuSCmd::CheckSynth);
                }
                Rule::ChcConstraintCmd => {
                    unimplemented!();
                    // let mut inner = cmd.into_inner();
                    // let vars = inner.next().unwrap();
                    // let term1 = inner.next().unwrap();
                    // let term2 = inner.next().unwrap();
                    // let sorted_vars = vars
                    //     .into_inner()
                    //     .map(|v| SortedVar::parse(v.as_str()))
                    //     .collect();
                    // problem.commands.push(SyGuSCmd::ChcConstraint(
                    //     sorted_vars,
                    //     SyGuSTerm::parse(term1.as_str()),
                    //     SyGuSTerm::parse(term2.as_str()),
                    // ));
                }
                Rule::ConstraintCmd => {
                    let inner = cmd.into_inner().next().unwrap();
                    let term = SyGuSTerm::parse(inner).unwrap();
                    problem.cmds.push(SyGuSCmd::Constraint(term));
                }
                Rule::DeclareVarCmd => {
                    let mut inner = cmd.into_inner();
                    let symbol = inner.next().unwrap().as_str().to_string();
                    if let Ok(sort) = Sort::parse(inner.next().unwrap()) {
                        problem.cmds.push(SyGuSCmd::DeclareVar(symbol, sort));
                    } else {
                        panic!("Invalid sort for variable: {}", symbol);
                    }
                }
                Rule::DeclareWeightCmd => {
                    unimplemented!();
                    // let mut inner = cmd.into_inner();
                    // let symbol = inner.next().unwrap().as_str().to_string();
                    // let attributes = inner.map(|a| Attribute::from_str(a.as_str())).collect();
                    // problem
                    //     .cmds
                    //     .push(SyGuSCmd::DeclareWeight(symbol, attributes));
                }
                Rule::InvConstraintCmd => {
                    unimplemented!();
                    // let mut inner = cmd.into_inner();
                    // problem.cmds.push(SyGuSCmd::InvConstraint(
                    //     inner.next().unwrap().as_str().to_string(),
                    //     inner.next().unwrap().as_str().to_string(),
                    //     inner.next().unwrap().as_str().to_string(),
                    //     inner.next().unwrap().as_str().to_string(),
                    // ));
                }
                Rule::OptimizeSynthCmd => {
                    unimplemented!();
                    // let mut inner = cmd.into_inner();
                    // let terms = inner.next().unwrap();
                    // let attributes = inner.map(|a| Attribute::from_str(a.as_str())).collect();
                    // let terms = terms
                    //     .into_inner()
                    //     .map(|t| SyGuSTerm::parse(t.as_str()))
                    //     .collect();
                    // problem
                    //     .cmds
                    //     .push(SyGuSCmd::OptimizeSynth(terms, attributes));
                }
                Rule::SetFeatureCmd => {
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
                Rule::SynthFunCmd => {
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
                    let synthfun = SynthFun {
                        name: symbol,
                        sorted_vars: sorted_var_list,
                        return_sort: ret_sort.unwrap(),
                        grammar_def,
                    };
                    problem.synthfuns.push(synthfun);
                }
                Rule::SMTCmd => {
                    let inner = cmd.into_inner().next().unwrap();
                    let smt_cmd = match inner.as_rule() {
                        Rule::DeclareDatatypeCmd => {
                            let mut inner = inner.into_inner();
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
                        Rule::DeclareDatatypesCmd => {
                            let mut inner = inner.into_inner();
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
                                                    inner
                                                        .map(|s| SortedVar::parse(s).unwrap())
                                                        .collect(),
                                                )
                                            })
                                            .collect(),
                                    )
                                })
                                .collect();
                            SMTCmd::DeclareDatatypes(sorts, decls)
                        }
                        Rule::DeclareSortCmd => {
                            let mut inner = inner.into_inner();
                            SMTCmd::DeclareSort(
                                inner.next().unwrap().as_str().to_string(),
                                inner.next().unwrap().as_str().parse::<usize>().unwrap(),
                            )
                        }
                        Rule::DefineFunCmd => {
                            // DefineFunCmd = { "(" ~ "define-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ SyGuSTerm ~ ")" }
                            let mut inner = inner.into_inner();
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
                            SMTCmd::DefineFun(
                                symbol,
                                sorted_var_list,
                                ret_sort.unwrap(),
                                term.unwrap(),
                            )
                        }
                        Rule::DefineSortCmd => {
                            let mut inner = inner.into_inner();
                            let sort = Sort::parse(inner.next().unwrap()).unwrap();
                            SMTCmd::DefineSort(inner.next().unwrap().as_str().to_string(), sort)
                        }
                        Rule::SetInfoCmd => {
                            let mut inner = inner.into_inner();
                            SMTCmd::SetInfo(
                                inner.next().unwrap().as_str().to_string(),
                                Literal::parse(inner.next().unwrap().as_str()),
                            )
                        }
                        Rule::SetLogicCmd => {
                            let mut inner = inner.into_inner();
                            SMTCmd::SetLogic(inner.next().unwrap().as_str().to_string())
                        }
                        Rule::SetOptionCmd => {
                            let mut inner = inner.into_inner();
                            SMTCmd::SetOption(
                                inner.next().unwrap().as_str().to_string(),
                                Literal::parse(inner.next().unwrap().as_str()),
                            )
                        }
                        _ => unreachable!(),
                    };
                    problem.cmds.push(SyGuSCmd::SMT(smt_cmd));
                }
                _ => unreachable!("Unknown command: {:?}", cmd),
            }
        }
        Ok(problem)
    }
}
