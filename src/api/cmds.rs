use crate::ast::*;

pub struct Cmd {
    kind: Option<CmdKind>,
    name: Option<String>,
    args: Vec<SortedVar>,
    ret_sort: Option<Sort>,
    body: Option<SyGuSTerm>,
    grammar: Option<Option<GrammarDef>>,
    arity: Option<usize>,
}

enum CmdKind {
    DeclareSort,
    DefineFun,
    SynthFun,
    DefineSort,
    Constraint,
}

impl Cmd {
    pub fn declare_sort(name: &str, arity: usize) -> Self {
        Self {
            kind: Some(CmdKind::DeclareSort),
            name: Some(name.to_string()),
            args: Vec::new(),
            ret_sort: None,
            arity: Some(arity),
            body: None,
            grammar: None,
        }
    }
    pub fn define_fun(name: &str) -> Self {
        Self {
            kind: Some(CmdKind::DefineFun),
            name: Some(name.to_string()),
            args: Vec::new(),
            ret_sort: None,
            body: None,
            grammar: None,
            arity: None,
        }
    }
    pub fn synth_fun(name: &str) -> Self {
        Self {
            kind: Some(CmdKind::SynthFun),
            name: Some(name.to_string()),
            args: Vec::new(),
            ret_sort: None,
            body: None,
            grammar: Some(None),
            arity: None,
        }
    }
    pub fn constraint() -> Self {
        Self {
            kind: Some(CmdKind::Constraint),
            name: None,
            args: Vec::new(),
            ret_sort: None,
            body: None,
            grammar: None,
            arity: None,
        }
    }
    pub fn arg(mut self, name: &str, sort: Sort) -> Self {
        self.args.push(SortedVar {
            name: name.to_string(),
            sort,
        });
        self
    }
    pub fn ret(mut self, sort: Sort) -> Self {
        self.ret_sort = Some(sort);
        self
    }
    pub fn body(mut self, term: SyGuSTerm) -> Self {
        self.body = Some(term);
        self
    }
    pub fn grammar(mut self, g: GrammarDef) -> Self {
        self.grammar = Some(Some(g));
        self
    }
    pub fn build(self) -> SyGuSCmd {
        match self.kind.unwrap() {
            CmdKind::DefineFun => SyGuSCmd::DefineFun(
                self.name.unwrap(),
                self.args,
                self.ret_sort.unwrap(),
                self.body.unwrap(),
            ),
            CmdKind::SynthFun => SyGuSCmd::SynthFun(
                self.name.unwrap(),
                self.args,
                self.ret_sort.unwrap(),
                self.grammar.unwrap(),
            ),
            CmdKind::DeclareSort => SyGuSCmd::DeclareSort(self.name.unwrap(), self.arity.unwrap()),
            CmdKind::Constraint => SyGuSCmd::Constraint(self.body.unwrap()),
            CmdKind::DefineSort => SyGuSCmd::DefineSort(self.name.unwrap(), vec![], self.ret_sort.unwrap()),
        }
    }
    pub fn define_sort(name: &str, sort: Sort) -> Self {
        Self {
            kind: Some(CmdKind::DefineSort),
            name: Some(name.to_string()),
            args: vec![],
            ret_sort: Some(sort),
            body: None,
            grammar: None,
            arity: None,
        }
    }
}
