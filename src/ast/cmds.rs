use crate::ast::{sorts::*, terms::*, utils::*};
use crate::parser::{Rule, SyGuSParser};
use crate::SyGuSParseError;
use derive_more::Display;
use itertools::Itertools;
use pest::iterators::Pair;
use pest::Parser;

#[derive(Debug, Clone, Display)]
/// Represents an enumeration of features supported by the SyGuS specification.
///
///
/// Provides variants for enabling or indicating support for different syntactic and semantic capabilities such as grammars, forward declarations, recursion, oracles, and weights, which facilitate detailed control over the synthesis process within SyGuS problem files.
pub enum SyGuSFeature {
    Grammars,
    FwdDecls,
    Recursion,
    Oracles,
    Weights,
}

type DTConsDecl = (String, Vec<SortedVar>);
type DTDecl = Vec<DTConsDecl>;

// SortDecl = { "(" ~ Symbol ~ Numeral ~ ")" }
#[derive(Debug, Clone, Display)]
/// A structure that holds sort declaration information.
/// It contains a field for the sort's identifier and another for its arity, allowing users to capture the essential properties of a sort in a concise manner.
#[display(fmt = "({} {})", symbol, arity)]
pub struct SortDecl {
    pub symbol: String,
    pub arity: usize,
}

#[derive(Debug, Clone, Display)]
/// Represents the set of available commands for specifying and processing SyGuS problems.
/// This item encapsulates command variants including assumptions on terms, synthesis checks, constraints, variable and weight declarations, invariant constraints, and optimized synthesis directives, as well as commands that set features, logics, synthesis functions with optional grammars, and integrate both Oracle and SMT specific instructions.
pub enum SyGuSCmd {
    #[display(fmt = "(assume {})", _0)]
    Assume(SyGuSTerm),
    #[display(fmt = "(check-synth)")]
    CheckSynth,
    // "(" ~ #SyGuSTkChcConstraint="chc-constraint" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ SyGuSTerm ~ ")"
    #[display(
        fmt = "(chc-constraint ({}) {} {})",
        "_0.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")",
        _1,
        _2
    )]
    ChcConstraint(Vec<SortedVar>, SyGuSTerm, SyGuSTerm),

    #[display(fmt = "(constraint {})", _0)]
    Constraint(SyGuSTerm),

    // "(" ~ "declare-var" ~ Symbol ~ Sort ~ ")"
    #[display(fmt = "(declare-var {} {})", _0, _1)]
    DeclareVar(String, Sort),

    // "(" ~ "declare-weight" ~ Symbol ~ Attribute* ~ ")"
    #[display(
        fmt = "(declare-weight {} {})",
        _0,
        "_1.iter().map(|a| format!(\"{}\", a)).collect::<Vec<_>>().join(\" \")"
    )]
    DeclareWeight(String, Vec<Attribute>),

    // SyGuSInvConstraintCmd = { "(" ~ "inv-constraint" ~ Symbol{4} ~ ")" }
    #[display(fmt = "(inv-constraint {} {} {} {})", _0, _1, _2, _3)]
    InvConstraint(String, String, String, String),

    // "(" ~ "optimize-synth" ~ "(" ~ SyGuSTerm* ~ ")" ~ Attribute* ~ ")"
    #[display(
        fmt = "(optimize-synth ({}) {})",
        "_0.iter().map(|t| format!(\"{}\", t)).collect::<Vec<_>>().join(\" \")",
        "_1.iter().map(|a| format!(\"{}\", a)).collect::<Vec<_>>().join(\" \")"
    )]
    OptimizeSynth(Vec<SyGuSTerm>, Vec<Attribute>),

    // "(" ~ "set-feature" ~ Symbol{2} ~ BoolConst ~ ")"
    #[display(fmt = "(set-feature {} {})", _0, _1)]
    SetFeature(SyGuSFeature, bool),

    // SynthFunCmd = { "(" ~ "synth-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ GrammarDef? ~ ")" }
    #[display(
        fmt = "(synth-fun {} ({}) {} {})",
        _0,
        "_1.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")",
        _2,
        "_3.as_ref().map_or(String::new(), |g| format!(\" {}\", g))"
    )]
    SynthFun(String, Vec<SortedVar>, Sort, Option<GrammarDef>),

    // #[display(fmt = "{}", _0)]
    // Oracle(OracleCmd),

    // SyGuSCmdOracleAssume = {"(" ~ #SyGuSTkOracleAssume="oracle-assume" ~ "(" ~ SortedVar* ~ ")" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ Symbol ~ ")"}
    #[display(
        fmt = "(oracle-assume ({}) ({}) {} {})",
        "_0.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")",
        "_1.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")",
        _2,
        _3
    )]
    OracleAssume(Vec<SortedVar>, Vec<SortedVar>, SyGuSTerm, String),
    // SyGuSCmdOracleConstraint = {"(" ~ #SyGuSTkOracleConstraint="oracle-constraint" ~ "(" ~ SortedVar* ~ ")" ~ "(" ~ SortedVar* ~ ")" ~ SyGuSTerm ~ Symbol ~ ")"}
    #[display(
        fmt = "(oracle-constraint ({}) ({}) {} {})",
        "_0.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")",
        "_1.iter().map(|v| format!(\"{}\", v)).collect::<Vec<_>>().join(\" \")",
        _2,
        _3
    )]
    OracleConstraint(Vec<SortedVar>, Vec<SortedVar>, SyGuSTerm, String),

    // SyGuSCmdDeclareOracleFun = {"(" ~ #SyGuSTkDeclareOracleFun="declare-oracle-fun" ~ Symbol ~ "(" ~ Sort* ~ ")" ~ Sort ~ Symbol ~ ")"}
    #[display(
        fmt = "(declare-oracle-fun {} ({}) {} {})",
        _0,
        "_1.iter().map(|s| format!(\"{}\", s)).collect::<Vec<_>>().join(\" \")",
        _2,
        _3
    )]
    DeclareOracleFun(String, Vec<Sort>, Sort, String),

    // SyGuSCmdOracleConstraintIO = {"(" ~ #SyGuSTkOracleConstraintIO="oracle-constraint-io" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(oracle-constraint-io {} {})", _0, _1)]
    OracleConstraintIO(String, String),

    // SyGuSCmdOracleConstraintCex = {"(" ~ #SyGuSTkOracleConstraintCex="oracle-constraint-cex" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(oracle-constraint-cex {} {})", _0, _1)]
    OracleConstraintCex(String, String),

    // SyGuSCmdOracleConstraintMembership = {"(" ~ #SyGuSTkOracleConstraintMembership="oracle-constraint-membership" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(oracle-constraint-membership {} {})", _0, _1)]
    OracleConstraintMembership(String, String),

    // SyGuSCmdOracleConstraintPosWitness = {"(" ~ #SyGuSTkOracleConstraintPoswitness="oracle-constraint-poswitness" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(oracle-constraint-poswitness {} {})", _0, _1)]
    OracleConstraintPosWitness(String, String),

    // SyGuSCmdOracleConstraintNegWitness = {"(" ~ #SyGuSTkOracleConstraintNegwitness="oracle-constraint-negwitness" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(oracle-constraint-negwitness {} {})", _0, _1)]
    OracleConstraintNegWitness(String, String),

    // SyGuSCmdDeclareCorrectnessOracle = {"(" ~ #SyGuSTkDeclareCorrectnessOracle="declare-correctness-oracle" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(declare-correctness-oracle {} {})", _0, _1)]
    DeclareCorrectnessOracle(String, String),

    // SyGuSCmdDeclareCorrectnessCexOracle = {"(" ~ #SyGuSTkDeclareCorrectnessCexOracle="declare-correctness-cex-oracle" ~ Symbol{2} ~ ")"}
    #[display(fmt = "(declare-correctness-cex-oracle {} {})", _0, _1)]
    DeclareCorrectnessCexOracle(String, String),

    // DeclareDatatypeCmd = { "(" ~ #SyGuSTkDeclareDatatype="declare-datatype" ~ Symbol ~ DTDecl ~ ")" }
    #[display(fmt = "(declare-datatype {} {})", _0, 
        "_1.iter().map(|(s, v)| format!(\"({} {})\", s, v.iter().map(|s| format!(\"{}\", s)).collect::<Vec<_>>().join(\" \"))).collect::<Vec<_>>().join(\" \")")]
    DeclareDatatype(String, DTDecl),

    // DeclareDatatypesCmd = { "(" ~ #SyGuSTkDeclareDatatypes="declare-datatypes" ~ "(" ~ SortDecl+ ~ ")" ~ "(" ~ DTDecl+ ~ ")" ~ ")" }
    #[display(
            fmt = "(declare-datatypes ({}) ({:?}))",
            "_0.iter().map(|s| format!(\"{}\", s)).collect::<Vec<_>>().join(\" \")",
            _1 // TODO
        )]
    DeclareDatatypes(Vec<SortDecl>, Vec<DTDecl>),

    // DeclareSortCmd = { "(" ~ #SyGuSTkDeclareSort="declare-sort" ~ Symbol ~ Numeral ~ ")" }
    #[display(fmt = "(declare-sort {} {})", _0, _1)]
    DeclareSort(String, usize),

    // DefineFunCmd = { "(" ~ #SyGuSTkDefineFun="define-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ SyGuSTerm ~ ")" }
    #[display(
        fmt = "(define-fun {} ({}) {} {})",
        _0,
        "_1.iter().map(|s| format!(\"{}\", s)).collect::<Vec<_>>().join(\" \")",
        _2,
        _3
    )]
    DefineFun(String, Vec<SortedVar>, Sort, SyGuSTerm),

    // DefineSortCmd = { "(" ~ #SyGuSTkDefineSort="define-sort" ~ Symbol ~ Sort ~ ")" }
    #[display(fmt = "(define-sort {} {})", _0, _1)]
    DefineSort(String, Sort),

    // SetInfoCmd = { "(" ~ #SyGuSTkSetInfo="set-info" ~ Keyword ~ Literal ~ ")" }
    #[display(fmt = "(set-info {} {})", _0, _1)]
    SetInfo(String, Literal),

    // SetLogicCmd = { "(" ~ #SyGuSTkSetLogic="set-logic" ~ Symbol ~ ")" }
    #[display(fmt = "(set-logic {})", _0)]
    SetLogic(String),

    // SetOptionCmd = { "(" ~ #SyGuSTkSetOption="set-option" ~ Keyword ~ Literal ~ ")" }
    #[display(fmt = "(set-option {} {})", _0, _1)]
    SetOption(String, Literal),
}

#[derive(Debug, Clone, Display)]
/// This struct serves as a container for the commands parsed from a SyGuS problem file.
/// It encapsulates a public vector of command representations, allowing further processing or analysis of the parsed input.
#[display(
    fmt = "{}",
    "cmds.iter().map(|c| format!(\"{}\", c)).collect::<Vec<_>>().join(\" \")"
)]
pub struct SyGuSFile {
    pub cmds: Vec<SyGuSCmd>,
}

impl SyGuSFile {
    /// Creates and returns a new instance of the abstract syntax tree file container.
    /// This function initializes the structure with an empty collection of commands, providing a clean slate for subsequently adding parsed instructions from a SyGuS problem file.
    pub fn new() -> Self {
        SyGuSFile { cmds: Vec::new() }
    }
    /// Parses a SyGuS problem file from a string input and returns its parsed representation.
    ///
    /// This function leverages the underlying parser to decode the problem specification by first extracting a single parsed file unit and then iterating through the commands it contains, excluding any end-of-input markers.
    /// Each command is successively parsed and accumulated into the overall representation, with any parsing errors propagated appropriately.
    ///
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
    /// Parses an input string into a SyGuS command representation.
    ///
    ///
    /// Transforms a string input by applying the SyGuS parser with the appropriate rule and then delegating to the command parsing logic.
    /// Returns a successfully parsed command or an error if the input does not adhere to the expected syntax.
    pub fn from_str(input: &str) -> Result<SyGuSCmd, SyGuSParseError> {
        let [cmd]: [_; 1] = SyGuSParser::parse(Rule::SyGuSCmd, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        SyGuSCmd::parse(cmd)
    }
    /// Parses an input pair from the syntax parser into its corresponding command representation as defined by the SyGuS specification.
    ///  
    ///
    /// Inspects the provided pair, matches it against established grammar rules, and converts it into the associated command variant.
    /// It handles a range of commands—such as assume, check-synth, constraint, declare-var, optimize-synth, set-feature, synth-fun, SMT commands, and oracle commands—by extracting the necessary components from the inner tokens.
    /// In the event of encountering an unsupported or unknown rule, it returns a parsing error, ensuring that only valid SyGuS commands are produced.
    pub fn parse(pair: Pair<'_, Rule>) -> Result<Self, SyGuSParseError> {
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
            Rule::SyGuSCmdOracleAssume => {
                let mut inner = pair.clone().into_inner();
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
                return Ok(SyGuSCmd::OracleAssume(
                    sorted_vars,
                    sorted_vars2,
                    term,
                    symbol,
                ));
            }
            Rule::SyGuSCmdOracleConstraint => {
                let mut inner = pair.clone().into_inner();
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
                return Ok(SyGuSCmd::OracleConstraint(
                    sorted_vars,
                    sorted_vars2,
                    term,
                    symbol,
                ));
            }
            Rule::SyGuSCmdDeclareOracleFun => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let sorts = inner
                    .next()
                    .unwrap()
                    .into_inner()
                    .map(|s| Sort::parse(s).unwrap())
                    .collect_vec();
                let ret_sort = Sort::parse(inner.next().unwrap()).unwrap();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::DeclareOracleFun(
                    symbol,
                    sorts,
                    ret_sort,
                    oracle_symbol,
                ));
            }
            Rule::SyGuSCmdOracleConstraintIO => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::OracleConstraintIO(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdOracleConstraintCex => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::OracleConstraintCex(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdOracleConstraintMembership => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::OracleConstraintMembership(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdOracleConstraintPosWitness => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::OracleConstraintPosWitness(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdOracleConstraintNegWitness => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::OracleConstraintNegWitness(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdDeclareCorrectnessOracle => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::DeclareCorrectnessOracle(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdDeclareCorrectnessCexOracle => {
                let mut inner = pair.clone().into_inner();
                let symbol = inner.next().unwrap().as_str().to_string();
                let oracle_symbol = inner.next().unwrap().as_str().to_string();
                return Ok(SyGuSCmd::DeclareCorrectnessCexOracle(symbol, oracle_symbol));
            }
            Rule::SyGuSCmdDeclareDatatype => {
                let mut inner = pair.clone().into_inner();
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
                return Ok(SyGuSCmd::DeclareDatatype(symbol, decl));
            }
            Rule::SyGuSCmdDeclareDatatypes => {
                let mut inner = pair.clone().into_inner();
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
                return Ok(SyGuSCmd::DeclareDatatypes(sorts, decls));
            }
            Rule::SyGuSCmdDeclareSort => {
                let mut inner = pair.clone().into_inner();
                return Ok(SyGuSCmd::DeclareSort(
                    inner.next().unwrap().as_str().to_string(),
                    inner.next().unwrap().as_str().parse::<usize>().unwrap(),
                ));
            }
            Rule::SyGuSCmdDefineFun => {
                // DefineFunCmd = { "(" ~ "define-fun" ~ Symbol ~ "(" ~ SortedVar* ~ ")" ~ Sort ~ SyGuSTerm ~ ")" }
                let mut inner = pair.clone().into_inner();
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
                return Ok(SyGuSCmd::DefineFun(
                    symbol,
                    sorted_var_list,
                    ret_sort.unwrap(),
                    term.unwrap(),
                ));
            }
            Rule::SyGuSCmdDefineSort => {
                let mut inner = pair.clone().into_inner();
                let sort = Sort::parse(inner.next().unwrap()).unwrap();
                return Ok(SyGuSCmd::DefineSort(
                    inner.next().unwrap().as_str().to_string(),
                    sort,
                ));
            }
            Rule::SyGuSCmdSetInfo => {
                let mut inner = pair.clone().into_inner();
                return Ok(SyGuSCmd::SetInfo(
                    inner.next().unwrap().as_str().to_string(),
                    Literal::from_str(inner.next().unwrap().as_str()),
                ));
            }
            Rule::SyGuSCmdSetLogic => {
                let mut inner = pair.clone().into_inner();
                return Ok(SyGuSCmd::SetLogic(
                    inner.next().unwrap().as_str().to_string(),
                ));
            }
            Rule::SyGuSCmdSetOption => {
                let mut inner = pair.clone().into_inner();
                return Ok(SyGuSCmd::SetOption(
                    inner.next().unwrap().as_str().to_string(),
                    Literal::from_str(inner.next().unwrap().as_str()),
                ));
            }
            _ => {
                println!("Unknown command: {:?}\n{:?}", pair.as_rule(), pair.as_str());
                return Err(SyGuSParseError::InvalidSyntax(format!(
                    "Unknown command: {:?}",
                    pair.as_rule()
                )));
            }
        }
    }
}
