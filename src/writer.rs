use std::io::{self, Write};

use crate::{
    Attribute, AttributeValue, DTConsDecl, GrammarDef, GroupedRuleList, Identifier, Index, Literal,
    SExpr, Sort, SortDecl, SortedVar, SyGuSCmd, SyGuSFeature, SyGuSGTerm, SyGuSTerm, VarBinding,
};

pub fn write_cmds<W: Write>(writer: &mut W, cmds: &[SyGuSCmd]) -> io::Result<()> {
    for (idx, cmd) in cmds.iter().enumerate() {
        if idx > 0 {
            writer.write_all(b"\n")?;
        }
        write_cmd(writer, cmd)?;
    }
    Ok(())
}

fn write_cmd<W: Write>(writer: &mut W, cmd: &SyGuSCmd) -> io::Result<()> {
    match cmd {
        SyGuSCmd::Assume(term) => {
            writer.write_all(b"(assume ")?;
            write_term(writer, term)?;
            writer.write_all(b")")
        }
        SyGuSCmd::CheckSynth => writer.write_all(b"(check-synth)"),
        SyGuSCmd::ChcConstraint(vars, lhs, rhs) => {
            writer.write_all(b"(chc-constraint (")?;
            write_spaced(writer, vars, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_term(writer, lhs)?;
            writer.write_all(b" ")?;
            write_term(writer, rhs)?;
            writer.write_all(b")")
        }
        SyGuSCmd::Constraint(term) => {
            writer.write_all(b"(constraint ")?;
            write_term(writer, term)?;
            writer.write_all(b")")
        }
        SyGuSCmd::DeclareVar(name, sort) => {
            write!(writer, "(declare-var {name} ")?;
            write_sort(writer, sort)?;
            writer.write_all(b")")
        }
        SyGuSCmd::DeclareWeight(name, attrs) => {
            write!(writer, "(declare-weight {name}")?;
            if !attrs.is_empty() {
                writer.write_all(b" ")?;
                write_spaced(writer, attrs, write_attribute)?;
            }
            writer.write_all(b")")
        }
        SyGuSCmd::InvConstraint(a, b, c, d) => {
            write!(writer, "(inv-constraint {a} {b} {c} {d})")
        }
        SyGuSCmd::OptimizeSynth(terms, attrs) => {
            writer.write_all(b"(optimize-synth (")?;
            write_spaced(writer, terms, write_term)?;
            writer.write_all(b")")?;
            if !attrs.is_empty() {
                writer.write_all(b" ")?;
                write_spaced(writer, attrs, write_attribute)?;
            }
            writer.write_all(b")")
        }
        SyGuSCmd::SetFeature(feature, value) => {
            writer.write_all(b"(set-feature ")?;
            write_feature(writer, feature)?;
            write!(writer, " {value})")
        }
        SyGuSCmd::SynthFun(name, vars, sort, grammar) => {
            write!(writer, "(synth-fun {name} (")?;
            write_spaced(writer, vars, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_sort(writer, sort)?;
            if let Some(grammar) = grammar {
                writer.write_all(b" ")?;
                write_grammar(writer, grammar)?;
            }
            writer.write_all(b")")
        }
        SyGuSCmd::OracleAssume(vars1, vars2, term, sym) => {
            writer.write_all(b"(oracle-assume (")?;
            write_spaced(writer, vars1, write_sorted_var)?;
            writer.write_all(b") (")?;
            write_spaced(writer, vars2, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_term(writer, term)?;
            write!(writer, " {sym})")
        }
        SyGuSCmd::OracleConstraint(vars1, vars2, term, sym) => {
            writer.write_all(b"(oracle-constraint (")?;
            write_spaced(writer, vars1, write_sorted_var)?;
            writer.write_all(b") (")?;
            write_spaced(writer, vars2, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_term(writer, term)?;
            write!(writer, " {sym})")
        }
        SyGuSCmd::DeclareOracleFun(name, domain, range, oracle) => {
            write!(writer, "(declare-oracle-fun {name} (")?;
            write_spaced(writer, domain, write_sort)?;
            writer.write_all(b") ")?;
            write_sort(writer, range)?;
            write!(writer, " {oracle})")
        }
        SyGuSCmd::OracleConstraintIO(a, b) => write!(writer, "(oracle-constraint-io {a} {b})"),
        SyGuSCmd::OracleConstraintCex(a, b) => write!(writer, "(oracle-constraint-cex {a} {b})"),
        SyGuSCmd::OracleConstraintMembership(a, b) => {
            write!(writer, "(oracle-constraint-membership {a} {b})")
        }
        SyGuSCmd::OracleConstraintPosWitness(a, b) => {
            write!(writer, "(oracle-constraint-poswitness {a} {b})")
        }
        SyGuSCmd::OracleConstraintNegWitness(a, b) => {
            write!(writer, "(oracle-constraint-negwitness {a} {b})")
        }
        SyGuSCmd::DeclareCorrectnessOracle(a, b) => {
            write!(writer, "(declare-correctness-oracle {a} {b})")
        }
        SyGuSCmd::DeclareCorrectnessCexOracle(a, b) => {
            write!(writer, "(declare-correctness-cex-oracle {a} {b})")
        }
        SyGuSCmd::DeclareDatatype(name, decl) => {
            write!(writer, "(declare-datatype {name} (")?;
            write_spaced(writer, decl, write_dt_cons_decl)?;
            writer.write_all(b"))")
        }
        SyGuSCmd::DeclareDatatypes(sorts, decls) => {
            writer.write_all(b"(declare-datatypes (")?;
            write_spaced(writer, sorts, write_sort_decl)?;
            writer.write_all(b") (")?;
            for (idx, decl) in decls.iter().enumerate() {
                if idx > 0 {
                    writer.write_all(b" ")?;
                }
                writer.write_all(b"(")?;
                write_spaced(writer, decl, write_dt_cons_decl)?;
                writer.write_all(b")")?;
            }
            writer.write_all(b"))")
        }
        SyGuSCmd::DeclareSort(name, arity) => write!(writer, "(declare-sort {name} {arity})"),
        SyGuSCmd::DefineFun(name, vars, sort, body) => {
            write!(writer, "(define-fun {name} (")?;
            write_spaced(writer, vars, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_sort(writer, sort)?;
            writer.write_all(b" ")?;
            write_term(writer, body)?;
            writer.write_all(b")")
        }
        SyGuSCmd::DefineSort(name, params, sort) => {
            write!(writer, "(define-sort {name} (")?;
            write_spaced_str(writer, params)?;
            writer.write_all(b") ")?;
            write_sort(writer, sort)?;
            writer.write_all(b")")
        }
        SyGuSCmd::SetInfo(key, value) => {
            write!(writer, "(set-info {key} ")?;
            write_literal(writer, value)?;
            writer.write_all(b")")
        }
        SyGuSCmd::SetLogic(logic) => write!(writer, "(set-logic {logic})"),
        SyGuSCmd::SetOption(key, value) => {
            write!(writer, "(set-option {key} ")?;
            write_literal(writer, value)?;
            writer.write_all(b")")
        }
    }
}

fn write_term<W: Write>(writer: &mut W, term: &SyGuSTerm) -> io::Result<()> {
    match term {
        SyGuSTerm::Identifier(id) => write_identifier(writer, id),
        SyGuSTerm::Literal(lit) => write_literal(writer, lit),
        SyGuSTerm::Application(id, args) => {
            writer.write_all(b"(")?;
            write_identifier(writer, id)?;
            writer.write_all(b" ")?;
            write_spaced(writer, args, write_term)?;
            writer.write_all(b")")
        }
        SyGuSTerm::Annotated(inner, attrs) => {
            writer.write_all(b"(! ")?;
            write_term(writer, inner)?;
            if !attrs.is_empty() {
                writer.write_all(b" ")?;
                write_spaced(writer, attrs, write_attribute)?;
            }
            writer.write_all(b")")
        }
        SyGuSTerm::Exists(vars, body) => {
            writer.write_all(b"(exists (")?;
            write_spaced(writer, vars, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_term(writer, body)?;
            writer.write_all(b")")
        }
        SyGuSTerm::Forall(vars, body) => {
            writer.write_all(b"(forall (")?;
            write_spaced(writer, vars, write_sorted_var)?;
            writer.write_all(b") ")?;
            write_term(writer, body)?;
            writer.write_all(b")")
        }
        SyGuSTerm::Let(bindings, body) => {
            writer.write_all(b"(let (")?;
            write_spaced(writer, bindings, write_var_binding)?;
            writer.write_all(b") ")?;
            write_term(writer, body)?;
            writer.write_all(b")")
        }
    }
}

fn write_grammar<W: Write>(writer: &mut W, grammar: &GrammarDef) -> io::Result<()> {
    if !grammar.sorted_vars.is_empty() {
        writer.write_all(b"(")?;
        write_spaced(writer, &grammar.sorted_vars, write_sorted_var)?;
        writer.write_all(b") ")?;
    }
    writer.write_all(b"(")?;
    write_spaced(writer, &grammar.grouped_rule_lists, write_grouped_rule_list)?;
    writer.write_all(b")")
}

fn write_grouped_rule_list<W: Write>(writer: &mut W, group: &GroupedRuleList) -> io::Result<()> {
    write!(writer, "({} ", group.symbol)?;
    write_sort(writer, &group.sort)?;
    writer.write_all(b" (")?;
    write_spaced(writer, &group.terms, write_gterm)?;
    writer.write_all(b"))")
}

fn write_gterm<W: Write>(writer: &mut W, term: &SyGuSGTerm) -> io::Result<()> {
    match term {
        SyGuSGTerm::Constant(sort) => {
            writer.write_all(b"(Constant ")?;
            write_sort(writer, sort)?;
            writer.write_all(b")")
        }
        SyGuSGTerm::Variable(sort) => {
            writer.write_all(b"(Variable ")?;
            write_sort(writer, sort)?;
            writer.write_all(b")")
        }
        SyGuSGTerm::SyGuSTerm(term) => write_term(writer, term),
    }
}

fn write_sorted_var<W: Write>(writer: &mut W, var: &SortedVar) -> io::Result<()> {
    write!(writer, "({} ", var.name)?;
    write_sort(writer, &var.sort)?;
    writer.write_all(b")")
}

fn write_var_binding<W: Write>(writer: &mut W, binding: &VarBinding) -> io::Result<()> {
    write!(writer, "({} ", binding.name)?;
    write_term(writer, &binding.term)?;
    writer.write_all(b")")
}

fn write_sort<W: Write>(writer: &mut W, sort: &Sort) -> io::Result<()> {
    match sort {
        Sort::Simple(id) => write_identifier(writer, id),
        Sort::Parameterized(id, subsorts) => {
            writer.write_all(b"(")?;
            write_identifier(writer, id)?;
            writer.write_all(b" ")?;
            write_spaced(writer, subsorts, write_sort)?;
            writer.write_all(b")")
        }
    }
}

fn write_identifier<W: Write>(writer: &mut W, id: &Identifier) -> io::Result<()> {
    match id {
        Identifier::Symbol(sym) => writer.write_all(sym.as_bytes()),
        Identifier::Indexed(sym, indices) => {
            writer.write_all(b"(")?;
            writer.write_all(sym.as_bytes())?;
            if !indices.is_empty() {
                writer.write_all(b" ")?;
                write_spaced(writer, indices, write_index)?;
            }
            writer.write_all(b")")
        }
    }
}

fn write_index<W: Write>(writer: &mut W, index: &Index) -> io::Result<()> {
    match index {
        Index::Numeral(n) => write!(writer, "{n}"),
        Index::Symbol(sym) => writer.write_all(sym.as_bytes()),
    }
}

fn write_literal<W: Write>(writer: &mut W, lit: &Literal) -> io::Result<()> {
    match lit {
        Literal::Numeral(n) => write!(writer, "{n}"),
        Literal::Decimal(n) => write!(writer, "{n}"),
        Literal::Bool(b) => write!(writer, "{b}"),
        Literal::HexConst(text) => {
            writer.write_all(b"#x")?;
            writer.write_all(text.as_bytes())
        }
        Literal::BinConst(text) => {
            writer.write_all(b"#b")?;
            writer.write_all(text.as_bytes())
        }
        Literal::StringConst(text) => writer.write_all(text.as_bytes()),
    }
}

fn write_attribute<W: Write>(writer: &mut W, attr: &Attribute) -> io::Result<()> {
    write!(writer, ":{}", attr.keyword)?;
    if let Some(value) = &attr.value {
        writer.write_all(b" ")?;
        write_attribute_value(writer, value)?;
    }
    Ok(())
}

fn write_attribute_value<W: Write>(writer: &mut W, value: &AttributeValue) -> io::Result<()> {
    match value {
        AttributeValue::SpecConstant(lit) => write_literal(writer, lit),
        AttributeValue::Symbol(sym) => writer.write_all(sym.as_bytes()),
        AttributeValue::SExprList(exprs) => {
            writer.write_all(b"(")?;
            write_spaced(writer, exprs, write_sexpr)?;
            writer.write_all(b")")
        }
    }
}

fn write_sexpr<W: Write>(writer: &mut W, expr: &SExpr) -> io::Result<()> {
    match expr {
        SExpr::SpecConstant(lit) => write_literal(writer, lit),
        SExpr::Symbol(sym) | SExpr::Reserved(sym) => writer.write_all(sym.as_bytes()),
        SExpr::Keyword(keyword) => write!(writer, ":{keyword}"),
        SExpr::SExprList(items) => {
            writer.write_all(b"(")?;
            write_spaced(writer, items, write_sexpr)?;
            writer.write_all(b")")
        }
    }
}

fn write_dt_cons_decl<W: Write>(writer: &mut W, decl: &DTConsDecl) -> io::Result<()> {
    write!(writer, "({} (", decl.name)?;
    write_spaced(writer, &decl.args, write_sorted_var)?;
    writer.write_all(b"))")
}

fn write_sort_decl<W: Write>(writer: &mut W, decl: &SortDecl) -> io::Result<()> {
    write!(writer, "({} {})", decl.symbol, decl.arity)
}

fn write_feature<W: Write>(writer: &mut W, feature: &SyGuSFeature) -> io::Result<()> {
    let text = match feature {
        SyGuSFeature::Grammars => "grammars",
        SyGuSFeature::FwdDecls => "fwd-decls",
        SyGuSFeature::Recursion => "recursion",
        SyGuSFeature::Oracles => "oracles",
        SyGuSFeature::Weights => "weights",
    };
    writer.write_all(text.as_bytes())
}

fn write_spaced<W: Write, T>(
    writer: &mut W,
    items: &[T],
    mut write_one: impl FnMut(&mut W, &T) -> io::Result<()>,
) -> io::Result<()> {
    for (idx, item) in items.iter().enumerate() {
        if idx > 0 {
            writer.write_all(b" ")?;
        }
        write_one(writer, item)?;
    }
    Ok(())
}

fn write_spaced_str<W: Write>(writer: &mut W, items: &[String]) -> io::Result<()> {
    for (idx, item) in items.iter().enumerate() {
        if idx > 0 {
            writer.write_all(b" ")?;
        }
        writer.write_all(item.as_bytes())?;
    }
    Ok(())
}
