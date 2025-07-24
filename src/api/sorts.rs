use crate::ast::{Identifier, Sort};

impl Sort {
    pub fn bool() -> Self {
        Sort::Simple(Identifier::Symbol("Bool".to_string()))
    }
    pub fn int() -> Self {
        Sort::Simple(Identifier::Symbol("Int".to_string()))
    }
    pub fn bitvec(width: usize) -> Self {
        Sort::Parameterized(
            Identifier::Symbol("_ BitVec".to_string()),
            vec![Sort::Simple(Identifier::Symbol(width.to_string()))],
        )
    }
}
