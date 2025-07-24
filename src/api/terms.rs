use crate::ast::*;

pub struct Term;

impl Term {
    // basic builder for terms.
    pub fn var(name: &str) -> SyGuSTerm {
        SyGuSTerm::Identifier(Identifier::Symbol(name.to_string()))
    }
    pub fn lit(lit: Literal) -> SyGuSTerm {
        SyGuSTerm::Literal(lit)
    }
    pub fn app(op: &str, args: Vec<SyGuSTerm>) -> SyGuSTerm {
        SyGuSTerm::Application(Identifier::Symbol(op.to_string()), args)
    }
    pub fn ite(cond: SyGuSTerm, then_t: SyGuSTerm, else_t: SyGuSTerm) -> SyGuSTerm {
        Self::app("ite", vec![cond, then_t, else_t])
    }
    pub fn let_binding(bindings: Vec<(String, SyGuSTerm)>, body: SyGuSTerm) -> SyGuSTerm {
        let vbs = bindings
            .into_iter()
            .map(|(name, term)| VarBinding {
                name,
                term: Box::new(term),
            })
            .collect();
        SyGuSTerm::Let(vbs, Box::new(body))
    }
    pub fn forall(vars: Vec<SortedVar>, body: SyGuSTerm) -> SyGuSTerm {
        SyGuSTerm::Forall(vars, Box::new(body))
    }
    pub fn exists(vars: Vec<SortedVar>, body: SyGuSTerm) -> SyGuSTerm {
        SyGuSTerm::Exists(vars, Box::new(body))
    }

    // builder for literals.
    pub fn bool(val: bool) -> SyGuSTerm {
        SyGuSTerm::Literal(Literal::Bool(val))
    }
    pub fn num(val: usize) -> SyGuSTerm {
        SyGuSTerm::Literal(Literal::Numeral(val))
    }
    pub fn bconst(val: u64, width: usize) -> SyGuSTerm {
        let s = format!("{:0width$b}", val, width = width);
        SyGuSTerm::Literal(Literal::BinConst(s))
    }
    pub fn hconst(val: &str) -> SyGuSTerm {
        SyGuSTerm::Literal(Literal::HexConst(val.to_string()))
    }
}

// builder for BitVec
pub struct BitVec;

impl BitVec {
    // BitVec literal
    pub fn const_(val: u64, width: usize) -> SyGuSTerm {
        Term::bconst(val, width)
    }

    // BitVec operations
    pub fn bvand(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvand", vec![x, y])
    }
    pub fn bvor(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvor", vec![x, y])
    }
    pub fn bvnot(x: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvnot", vec![x])
    }
    pub fn bvxor(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvxor", vec![x, y])
    }
    pub fn bvadd(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvadd", vec![x, y])
    }
    pub fn bvsub(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvsub", vec![x, y])
    }
    pub fn bvmul(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvmul", vec![x, y])
    }
    pub fn bvudiv(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvudiv", vec![x, y])
    }
    pub fn bvurem(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvurem", vec![x, y])
    }
    pub fn bvsdiv(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvsdiv", vec![x, y])
    }
    pub fn bvsrem(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvsrem", vec![x, y])
    }
    pub fn bvshl(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvshl", vec![x, y])
    }
    pub fn bvlshr(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvlshr", vec![x, y])
    }
    pub fn bvashr(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvashr", vec![x, y])
    }

    // comparison operations
    pub fn bvult(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvult", vec![x, y])
    }
    pub fn bvule(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvule", vec![x, y])
    }
    pub fn bvugt(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvugt", vec![x, y])
    }
    pub fn bvuge(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvuge", vec![x, y])
    }
    pub fn bvslt(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvslt", vec![x, y])
    }
    pub fn bvsle(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvsle", vec![x, y])
    }
    pub fn bvsgt(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvsgt", vec![x, y])
    }
    pub fn bvsge(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("bvsge", vec![x, y])
    }

    // type conversion
    pub fn concat(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("concat", vec![x, y])
    }
    pub fn extract(high: usize, low: usize, x: SyGuSTerm) -> SyGuSTerm {
        let extract_id = Identifier::Indexed(
            "_ extract".to_string(),
            vec![Index::Numeral(high), Index::Numeral(low)],
        );
        SyGuSTerm::Application(extract_id, vec![x])
    }
}

// builder for Int
pub struct Int;

impl Int {
    // Int literal
    pub fn const_(val: usize) -> SyGuSTerm {
        Term::num(val)
    }

    // Int operations
    pub fn add(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("+", vec![x, y])
    }
    pub fn sub(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("-", vec![x, y])
    }
    pub fn mul(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("*", vec![x, y])
    }
    pub fn div(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("div", vec![x, y])
    }
    pub fn mod_(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("mod", vec![x, y])
    }
    pub fn abs(x: SyGuSTerm) -> SyGuSTerm {
        Term::app("abs", vec![x])
    }

    // comparison operations
    pub fn lt(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("<", vec![x, y])
    }
    pub fn le(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("<=", vec![x, y])
    }
    pub fn gt(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app(">", vec![x, y])
    }
    pub fn ge(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app(">=", vec![x, y])
    }
}

// builder for Bool
pub struct Bool;

impl Bool {
    // Bool literal
    pub fn true_() -> SyGuSTerm {
        Term::bool(true)
    }
    pub fn false_() -> SyGuSTerm {
        Term::bool(false)
    }

    // Bool operations
    pub fn and(args: Vec<SyGuSTerm>) -> SyGuSTerm {
        Term::app("and", args)
    }
    pub fn or(args: Vec<SyGuSTerm>) -> SyGuSTerm {
        Term::app("or", args)
    }
    pub fn not(x: SyGuSTerm) -> SyGuSTerm {
        Term::app("not", vec![x])
    }
    pub fn implies(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("=>", vec![x, y])
    }
    pub fn xor(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("xor", vec![x, y])
    }
    pub fn eq(x: SyGuSTerm, y: SyGuSTerm) -> SyGuSTerm {
        Term::app("=", vec![x, y])
    }
    pub fn distinct(args: Vec<SyGuSTerm>) -> SyGuSTerm {
        Term::app("distinct", args)
    }
}
