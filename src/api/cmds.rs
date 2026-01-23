use crate::ast::*;

pub struct Cmd {
    kind: CmdState,
}

enum CmdState {
    Ready(SyGuSCmd),
    DefineFun {
        name: String,
        args: Vec<SortedVar>,
        ret_sort: Option<Sort>,
        body: Option<SyGuSTerm>,
    },
    SynthFun {
        name: String,
        args: Vec<SortedVar>,
        ret_sort: Option<Sort>,
        grammar: Option<GrammarDef>,
    },
    Constraint {
        body: Option<SyGuSTerm>,
    },
}

#[derive(Debug, Clone)]
pub struct CmdBuildError {
    kind: &'static str,
    name: Option<String>,
    missing: Vec<&'static str>,
}

impl std::fmt::Display for CmdBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self
            .name
            .as_ref()
            .map_or(String::from("<anonymous>"), |n| n.clone());
        write!(
            f,
            "incomplete {} command (name: {}), missing: {}",
            self.kind,
            name,
            self.missing.join(", ")
        )
    }
}

impl Cmd {
    pub fn declare_sort(name: &str, arity: usize) -> Self {
        Self {
            kind: CmdState::Ready(SyGuSCmd::DeclareSort(name.to_string(), arity)),
        }
    }
    pub fn define_fun(name: &str) -> Self {
        Self {
            kind: CmdState::DefineFun {
                name: name.to_string(),
                args: Vec::new(),
                ret_sort: None,
                body: None,
            },
        }
    }
    pub fn synth_fun(name: &str) -> Self {
        Self {
            kind: CmdState::SynthFun {
                name: name.to_string(),
                args: Vec::new(),
                ret_sort: None,
                grammar: None,
            },
        }
    }
    pub fn constraint() -> Self {
        Self {
            kind: CmdState::Constraint { body: None },
        }
    }
    pub fn arg(mut self, name: &str, sort: Sort) -> Self {
        let var = SortedVar {
            name: name.to_string(),
            sort,
        };
        match &mut self.kind {
            CmdState::DefineFun { args, .. } | CmdState::SynthFun { args, .. } => {
                args.push(var);
            }
            _ => {}
        }
        self
    }
    pub fn ret(mut self, sort: Sort) -> Self {
        match &mut self.kind {
            CmdState::DefineFun { ret_sort, .. } | CmdState::SynthFun { ret_sort, .. } => {
                *ret_sort = Some(sort);
            }
            _ => {}
        }
        self
    }
    pub fn body(mut self, term: SyGuSTerm) -> Self {
        match &mut self.kind {
            CmdState::DefineFun { body, .. } | CmdState::Constraint { body } => {
                *body = Some(term);
            }
            _ => {}
        }
        self
    }
    pub fn grammar(mut self, g: GrammarDef) -> Self {
        match &mut self.kind {
            CmdState::SynthFun { grammar, .. } => {
                *grammar = Some(g);
            }
            _ => {}
        }
        self
    }
    pub fn try_build(self) -> Result<SyGuSCmd, CmdBuildError> {
        match self.kind {
            CmdState::Ready(cmd) => Ok(cmd),
            CmdState::DefineFun {
                name,
                args,
                ret_sort,
                body,
            } => {
                let mut missing = Vec::new();
                if ret_sort.is_none() {
                    missing.push("return sort");
                }
                if body.is_none() {
                    missing.push("body");
                }
                if !missing.is_empty() {
                    return Err(CmdBuildError {
                        kind: "define-fun",
                        name: Some(name),
                        missing,
                    });
                }
                Ok(SyGuSCmd::DefineFun(
                    name,
                    args,
                    ret_sort.unwrap(),
                    body.unwrap(),
                ))
            }
            CmdState::SynthFun {
                name,
                args,
                ret_sort,
                grammar,
            } => {
                if ret_sort.is_none() {
                    return Err(CmdBuildError {
                        kind: "synth-fun",
                        name: Some(name),
                        missing: vec!["return sort"],
                    });
                }
                Ok(SyGuSCmd::SynthFun(name, args, ret_sort.unwrap(), grammar))
            }
            CmdState::Constraint { body } => {
                if body.is_none() {
                    return Err(CmdBuildError {
                        kind: "constraint",
                        name: None,
                        missing: vec!["body"],
                    });
                }
                Ok(SyGuSCmd::Constraint(body.unwrap()))
            }
        }
    }
    pub fn build(self) -> SyGuSCmd {
        self.try_build().unwrap_or_else(|err| panic!("{err}"))
    }
    pub fn define_sort(name: &str, sort: Sort) -> Self {
        Self {
            kind: CmdState::Ready(SyGuSCmd::DefineSort(name.to_string(), vec![], sort)),
        }
    }
}
