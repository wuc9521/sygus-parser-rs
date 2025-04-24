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

    #[display(fmt = "{}", _0)]
    Oracle(OracleCmd),

    #[display(fmt = "{}", _0)]
    SMT(SMTCmd),
}

#[derive(Debug, Clone, Display)]
/// This code defines an interface representing various oracle commands used to express oracle-related operations in SyGuS problems.
/// Each variant encapsulates a specific kind of oracle command, capturing the parameters required to represent assumptions, constraints, and declarations related to oracle functionality.
///
/// The first two variants support commands that express assumptions and constraints through lists of sorted variables, a term, and an associated identifier.
/// Additional variants facilitate the declaration of oracle functions, handling of I/O commands, counterexample-based constraints, membership tests, and witness constraints, as well as commands for asserting oracle correctness.
pub enum OracleCmd {
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
}

impl OracleCmd {
    /// Converts a string slice into a structured oracle command result.
    ///
    /// This method takes an input string, applies the parsing rule for oracle commands, and converts the obtained parse tree into a corresponding oracle command object.
    /// If the input does not conform to the expected format, it returns an error detailing the parsing issue.
    ///
    pub fn from_str(input: &str) -> Result<OracleCmd, SyGuSParseError> {
        let [cmd]: [_; 1] = SyGuSParser::parse(Rule::SyGuSCmdOracle, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        OracleCmd::parse(cmd)
    }
    /// Parses a Pest pair representation into an oracle command variant according to the SyGuS specification.
    ///
    /// This function analyzes the input pair by matching the underlying rule and then translates it into one of several supported command variants such as oracle assume, oracle constraint, declare oracle function, and various correctness or witness constraints.
    /// It returns the corresponding oracle command on successful matching, or an error describing an invalid syntax if the input does not conform to any recognized form.
    ///
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
                Rule::SyGuSCmdOracleConstraint => {
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

#[derive(Debug, Clone, Display)]
/// This enumeration encapsulates commands related to SMT processing, facilitating the specification of various SMT actions.
///
/// It supports operations such as declaring datatypes and sorts, defining functions and sorts, and configuring SMT options like logic, information, or additional parameters.
/// Each variant represents a distinct command interface used to express the corresponding SMT directive within the parsing framework.
///
pub enum SMTCmd {
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

impl SMTCmd {
    /// Constructs an SMT command from its string representation.
    ///
    ///
    /// Parses the given input string according to the corresponding syntax rule and returns either the successfully constructed SMT command or a parse error.
    pub fn from_str(input: &str) -> Result<SMTCmd, SyGuSParseError> {
        let [cmd]: [_; 1] = SyGuSParser::parse(Rule::SyGuSCmdSMT, input)?
            .collect_vec()
            .try_into()
            .unwrap();
        SMTCmd::parse(cmd)
    }
    /// Parses a pest parse tree pair into an SMT command.
    ///
    /// This function inspects the rule associated with the input pair and returns a corresponding SMT command variant based on the recognized input construct.
    /// It handles various command types such as datatype declarations, function and sort definitions, setting information, logic, and options, delegating parsing tasks to the appropriate helper methods for inner tokens.
    /// On encountering an unexpected rule, it returns a parsing error, ensuring robust handling of invalid syntax.
    ///
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
                )));
            }
        }
    }
}
