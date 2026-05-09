use crate::ast::{Identifier, Index, Literal, SyGuSTerm};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BuiltinOp {
    Not,
    And,
    Or,
    Eq,
    Ite,
    BvNot,
    BvAnd,
    BvOr,
    BvXor,
    Concat,
    Extract { hi: usize, lo: usize },
}

impl Identifier {
    pub fn as_symbol_name(&self) -> Option<&str> {
        match self {
            Identifier::Symbol(sym) => Some(sym.as_str()),
            Identifier::Indexed(_, _) => None,
        }
    }

    pub fn as_indexed(&self) -> Option<(&str, &[Index])> {
        match self {
            Identifier::Symbol(_) => None,
            Identifier::Indexed(sym, indices) => Some((sym.as_str(), indices.as_slice())),
        }
    }

    pub fn as_builtin_op(&self) -> Option<BuiltinOp> {
        match self {
            Identifier::Symbol(sym) => match sym.as_str() {
                "not" => Some(BuiltinOp::Not),
                "and" => Some(BuiltinOp::And),
                "or" => Some(BuiltinOp::Or),
                "=" => Some(BuiltinOp::Eq),
                "ite" => Some(BuiltinOp::Ite),
                "bvnot" => Some(BuiltinOp::BvNot),
                "bvand" => Some(BuiltinOp::BvAnd),
                "bvor" => Some(BuiltinOp::BvOr),
                "bvxor" => Some(BuiltinOp::BvXor),
                "concat" => Some(BuiltinOp::Concat),
                _ => None,
            },
            Identifier::Indexed(sym, indices) if sym == "_ extract" && indices.len() == 2 => {
                let [Index::Numeral(hi), Index::Numeral(lo)] = indices.as_slice() else {
                    return None;
                };
                Some(BuiltinOp::Extract { hi: *hi, lo: *lo })
            }
            _ => None,
        }
    }
}

impl Literal {
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Literal::Bool(value) => Some(*value),
            _ => None,
        }
    }

    pub fn as_bin_const_bits(&self) -> Option<&str> {
        match self {
            Literal::BinConst(bits) => Some(bits.as_str()),
            _ => None,
        }
    }

    pub fn as_single_bit_bin_const(&self) -> Option<bool> {
        let bits = self.as_bin_const_bits()?;
        if bits.len() != 1 {
            return None;
        }
        match bits.as_bytes().first().copied() {
            Some(b'0') => Some(false),
            Some(b'1') => Some(true),
            _ => None,
        }
    }
}

impl SyGuSTerm {
    pub fn as_var_name(&self) -> Option<&str> {
        let SyGuSTerm::Identifier(id) = self else {
            return None;
        };
        id.as_symbol_name()
    }

    pub fn as_lit(&self) -> Option<&Literal> {
        match self {
            SyGuSTerm::Literal(lit) => Some(lit),
            _ => None,
        }
    }

    pub fn as_bool_const(&self) -> Option<bool> {
        self.as_lit()?.as_bool()
    }

    pub fn as_single_bit_bv_const(&self) -> Option<bool> {
        self.as_lit()?.as_single_bit_bin_const()
    }

    pub fn as_app(&self) -> Option<(&Identifier, &[SyGuSTerm])> {
        match self {
            SyGuSTerm::Application(id, args) => Some((id, args.as_slice())),
            _ => None,
        }
    }

    pub fn as_op(&self) -> Option<(BuiltinOp, &[SyGuSTerm])> {
        let (id, args) = self.as_app()?;
        Some((id.as_builtin_op()?, args))
    }

    pub fn as_extract(&self) -> Option<(usize, usize, &SyGuSTerm)> {
        let (op, args) = self.as_op()?;
        let BuiltinOp::Extract { hi, lo } = op else {
            return None;
        };
        if args.len() != 1 {
            return None;
        }
        Some((hi, lo, &args[0]))
    }
}
