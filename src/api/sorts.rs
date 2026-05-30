use crate::ast::{Identifier, Index, Sort};

impl Sort {
    pub fn bool() -> Self {
        Sort::Simple(Identifier::Symbol("Bool".to_string()))
    }
    pub fn int() -> Self {
        Sort::Simple(Identifier::Symbol("Int".to_string()))
    }

    pub fn real() -> Self {
        Sort::Simple(Identifier::Symbol("Real".to_string()))
    }

    pub fn string() -> Self {
        Sort::Simple(Identifier::Symbol("String".to_string()))
    }
    pub fn bitvec(width: usize) -> Self {
        // Mirror what the parser emits for `(_ BitVec N)`: a Simple sort
        // whose identifier is the indexed form `(_ BitVec N)`. Earlier this
        // function built `Parameterized(Symbol("_ BitVec"), …)` which
        // displayed correctly but had the wrong AST shape and the wrong
        // symbol name, breaking equality and downstream lookups.
        Sort::Simple(Identifier::Indexed(
            "BitVec".to_string(),
            vec![Index::Numeral(width)],
        ))
    }
    pub fn from_name(name: &str) -> Self {
        Sort::Simple(Identifier::Symbol(name.to_string()))
    }
    pub fn arrow(from: Sort, to: Sort) -> Self {
        Sort::Parameterized(
            Identifier::Symbol("->".to_string()),
            vec![from, to],
        )
    }
}
