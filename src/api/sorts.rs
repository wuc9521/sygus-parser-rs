use crate::ast::{Identifier, Sort};

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
        Sort::Parameterized(
            Identifier::Symbol("_ BitVec".to_string()),
            vec![Sort::Simple(Identifier::Symbol(width.to_string()))],
        )
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
