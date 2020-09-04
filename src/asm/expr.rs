//! Everything needed to handle expression trees.
//! 
//! The important types are `Expr`, which represents an expression tree, and `SymbolTable`, which is the special collection type used for evaluation.

use std::hash::Hash;
use std::collections::HashMap;
use std::cell::RefCell;
use std::io::{self, Read, Write};

#[cfg(test)]
use std::io::Cursor;

use num_traits::FromPrimitive;

use crate::common::serialization::*;

/// The supported operations in an expr.
/// 
/// For safety, in nearly all contexts it is considered illegal to mix integral and floating-point values.
/// An important exception is the ternary conditional, which is allowed due to the fact that it can short circuit and is compile-time only.
#[derive(Debug, Clone, Copy, FromPrimitive, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum OP {
    /// A special operation that can be used as a placeholder when building expression trees.
    /// Attempting to evaluate an expression containing this op code will panic.
    Invalid,

    // binary ops

    Mul,
    SDiv, SMod,
    UDiv, UMod,
    Add, Sub,

    SHL, SHR, SAR,

    SLess, SLessE, SGreat, SGreatE,
    ULess, ULessE, UGreat, UGreatE,
    Eq, Neq,

    BitAnd, BitXor, BitOr,
    LogAnd, LogOr,

    // unary ops

    Neg,
    BitNot, LogNot,
    
    // function-like operators

    Int, Float, // convert int <-> float
    Floor, Ceil, Round, Trunc,

    Repr64, Repr32,   // interpret float as IEEE-754 encoded int
    Float64, Float32, // interpret IEEE-754 encoded int as float
    Prec64, Prec32,   // explicit precision truncations

    // special

    /// Used for ternary conditionals.
    /// The left branch is the condition,
    /// and the right branch is a `Pair` whose left and right sub-branches are the two values to select.
    Condition,
    /// A special op code which is illegal in all contexts other than the immediate right child of `Condition`.
    Pair,
}
impl BinaryWrite for OP {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        (*self as u8).bin_write(f)
    }
}
impl BinaryRead for OP {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<OP> {
        match OP::from_u8(u8::bin_read(f)?) {
            Some(op) => Ok(op),
            None => Err(io::ErrorKind::InvalidData.into()),
        }
    }
}
#[test]
fn test_invalid_op_decode() {
    let mut f = Cursor::new(Vec::new());
    f.write_all(&[45]).unwrap();
    f.set_position(0);
    match OP::bin_read(&mut f) {
        Err(e) if e.kind() == io::ErrorKind::InvalidData => (),
        _ => panic!("didn't fail"),
    }
}

/// An int or float token in an expr.
/// 
/// The assembler doesn't know or care about signed/unsigned literals, so all integers are stored as raw `u64`.
/// They are contextually treated as signed/unsigned based on operators that are applied to them.
#[derive(Debug, Clone, Copy)]
pub enum Value {
    Integral(u64),
    Floating(f64),
}
impl BinaryWrite for Value {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            Value::Integral(v) => {
                0u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Floating(v) => {
                1u8.bin_write(f)?;
                v.to_bits().bin_write(f)
            }
        }
    }
}
impl BinaryRead for Value {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Value> {
        match u8::bin_read(f)? {
            0 => Ok(Value::Integral(u64::bin_read(f)?)),
            1 => Ok(Value::Floating(u64::bin_read(f).map(f64::from_bits)?)),
            _ => Err(io::ErrorKind::InvalidData.into()),
        }
    }
}
impl From<u64> for Value {
    fn from(val: u64) -> Self {
        Value::Integral(val)
    }
}
impl From<f64> for Value {
    fn from(val: f64) -> Self {
        Value::Floating(val)
    }
}

/// An unevaluated expression tree.
/// 
/// Attempting to evaluate an ill-formed expression tree will panic.
/// Unary operations use only the left branch, but will panic if the right branch is also present.
#[derive(Debug, Clone)]
pub struct Uneval {
    pub op: OP,
    pub left: Option<Box<Expr>>,
    pub right: Option<Box<Expr>>,
}
impl BinaryWrite for Uneval {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.op.bin_write(f)?;
        self.left.bin_write(f)?;
        self.right.bin_write(f)
    }
}
impl BinaryRead for Uneval {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Uneval> {
        let op = BinaryRead::bin_read(f)?;
        let left = BinaryRead::bin_read(f)?;
        let right = BinaryRead::bin_read(f)?;
        Ok(Uneval { op, left, right })
    }
}

/// Holds the information needed to create an instance of `Expr`.
/// 
/// # Example
/// ```
/// # use csx64::asm::expr::*;
/// let ex: Expr = ExprData::Ident("foo".into()).into();
/// let ey: Expr = 12.into(); // thanks to convenience functions, ExprData::Value is even simpler
/// println!("{:?} {:?}", ex, ey);
/// ```
#[derive(Clone)]
pub enum ExprData {
    Value(Value),
    Uneval(Uneval),
    Ident(String),
}
impl BinaryWrite for ExprData {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            ExprData::Value(value) => {
                0u8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Uneval(uneval) => {
                1u8.bin_write(f)?;
                uneval.bin_write(f)
            }
            ExprData::Ident(ident) => {
                2u8.bin_write(f)?;
                ident.bin_write(f)
            }
        }
    }
}
impl BinaryRead for ExprData {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<ExprData> {
        match u8::bin_read(f)? {
            0 => Ok(ExprData::Value(BinaryRead::bin_read(f)?)),
            1 => Ok(ExprData::Uneval(BinaryRead::bin_read(f)?)),
            2 => Ok(ExprData::Ident(BinaryRead::bin_read(f)?)),
            _ => Err(io::ErrorKind::InvalidData.into()),
        }
    }
}
impl std::fmt::Debug for ExprData {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            ExprData::Value(val) => write!(f, "{:?}", val),
            ExprData::Uneval(uneval) => write!(f, "{:?}", uneval),
            ExprData::Ident(ident) => write!(f, "Ident({})", ident),
        }
    }
}
/// Convenience for creating instances of `ExprData::Value`.
impl<T> From<T> for ExprData where Value: From<T> {
    fn from(val: T) -> Self {
        ExprData::Value(val.into())
    }
}
/// Convenience for creating instances of `ExprData::Uneval` for binary ops.
impl<T, U> From<(OP, T, U)> for ExprData where Expr: From<T> + From<U> {
    fn from(vals: (OP, T, U)) -> Self {
        ExprData::Uneval(Uneval { op: vals.0, left: Some(Box::new(vals.1.into())), right: Some(Box::new(vals.2.into())) })
    }
}
/// Convenience for creating instances of `ExprData::Uneval` for unary ops.
impl<T> From<(OP, T)> for ExprData where Expr: From<T> {
    fn from(vals: (OP, T)) -> Self {
        ExprData::Uneval(Uneval { op: vals.0, left: Some(Box::new(vals.1.into())), right: None })
    }
}

/// An expression.
/// 
/// This is an effectively-immutable (see `SymbolTable` example) numeric syntax tree.
/// It is completely opaque aside from getting the value via `eval()`, and should be constructed via `ExprData`.
/// 
/// Attempting to evaluate an ill-formed expression will panic.
#[derive(Clone)]
pub struct Expr {
    data: RefCell<ExprData>,
}
impl BinaryWrite for Expr {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.data.bin_write(f)
    }
}
impl BinaryRead for Expr {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Expr> {
        Ok(Expr { data: BinaryRead::bin_read(f)? })
    }
}
impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", &*self.data.borrow())
    }
}
/// Convenience for creating expressions from the raw type `ExprData`.
impl<T> From<T> for Expr where ExprData: From<T> {
    fn from(val: T) -> Self {
        Expr { data: RefCell::new(val.into()) }
    }
}

/// A appendonly map-like collection of defined symbols.
/// 
/// Importantly, an instance of this type is used during assembly/linking to facilitate pre- and user-defined symbols.
/// 
/// # Example
/// ```
/// # use csx64::asm::expr::*;
/// let mut symbols = SymbolTable::new();
/// symbols.define("foo".into(), 2.into()).unwrap();
/// 
/// let expr: Expr = (OP::Add, 2, ExprData::Ident("foo".into())).into();
/// println!("before: {:?}", expr);
/// assert!(matches!(expr.eval(&symbols).unwrap(), Value::Integral(4)));
/// println!("after:  {:?}", expr);
/// ```
/// 
/// Note that in the above example `expr` was technically modified despite `eval()` being an immutable method.
/// This is what will be referred to as auto-reducing logic: the value of `expr` isn't actually different, it's just a simpler representation of the same value.
/// From a rust perspective, this is perfectly safe because, aside from using debug formatting, it would be impossible to know anything had happened at all
/// due to the fact that `SymbolTable` is appendonly and `Expr` is opaque.
/// 
/// The way this is done is that any sub-expression in the expression tree which successfully evaluates is replaced with a value node with equivalent content.
/// Because of this, if an `Expr` is evaluated using a given symbol table, it should typically never be evaluated with any other symbol table, lest the final value be potentially corrupted.
/// Best practice has that there should be only one symbol table, which is what the assembly and linking functions included in this crate do implicitly.
#[derive(Default, Clone)]
pub struct SymbolTable {
    symbols: HashMap<String, Expr>,
}
impl BinaryWrite for SymbolTable {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.symbols.bin_write(f)
    }
}
impl BinaryRead for SymbolTable {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<SymbolTable> {
        Ok(SymbolTable { symbols: BinaryRead::bin_read(f)? })
    }
}
impl std::fmt::Debug for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        for (k, v) in self.iter() {
            writeln!(f, "{} := {:?}", k, v)?;
        }
        Ok(())
    }
}

/// The specific reason why an illegal operation failed.
#[derive(Debug, Clone, Copy)]
pub enum IllegalReason {
    MixIntFloat,
    DivideByZero,
    UnsignedFloat,
    BitwiseFloat,
    TruthyFloat,
    CyclicDependency,
    /// A sort of wild-card to catch any invalid-arg-related problem that isn't covered by another category.
    /// The stored string explains even more specifically what went wrong.
    /// These are typically issued by function-like operators.
    InvalidArg(&'static str),
}

/// The reason why an expression failed to be evaluated.
/// 
/// `Illegal` deontes an unrecoverable failure during assembly or linking.
/// Any other type of failure can be recovered so long as all problems are resolved at least by the last phase of linking.
#[derive(Debug)]
pub enum EvalError {
    /// Denotes that the user did something illegal (e.g. incorrect types to operators or cyclic dependencies).
    /// If this is encountered during assembly/linking, it is considered a hard error.
    /// The stored value further explains what went wrong.
    Illegal(IllegalReason),
    /// Denotes that evaluation failed because the stored symbol name was not defined.
    UndefinedSymbol(String),
}

// ----------------------------------------------------------------------------------------------

fn all_legal(res: &[&Result<Value, EvalError>]) -> Result<(), EvalError> {
    for &x in res.iter() {
        if let Err(EvalError::Illegal(reason)) = x {
            return Err(EvalError::Illegal(*reason));
        }
    }
    Ok(())
}
#[test]
fn test_all_legal() {
    assert!(all_legal(&[&Ok(34.into()), &Ok(3.42.into())]).is_ok());
    assert!(all_legal(&[&Ok(Value::Integral(54)), &Err(EvalError::UndefinedSymbol("heloo".to_string()))]).is_ok());
    assert!(all_legal(&[&Err(EvalError::UndefinedSymbol("heloo".to_string())), &Err(EvalError::UndefinedSymbol("heloo".to_string()))]).is_ok());
    match all_legal(&[&Err(EvalError::Illegal(IllegalReason::UnsignedFloat)), &Err(EvalError::UndefinedSymbol("heloo".to_string()))]) {
        Err(EvalError::Illegal(IllegalReason::UnsignedFloat)) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Err(EvalError::UndefinedSymbol("heloo".to_string())), &Err(EvalError::Illegal(IllegalReason::MixIntFloat))]) {
        Err(EvalError::Illegal(IllegalReason::MixIntFloat)) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Ok(Value::Integral(463)), &Err(EvalError::Illegal(IllegalReason::BitwiseFloat))]) {
        Err(EvalError::Illegal(IllegalReason::BitwiseFloat)) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Err(EvalError::Illegal(IllegalReason::InvalidArg("message"))), &Err(EvalError::Illegal(IllegalReason::TruthyFloat))]) {
        Err(EvalError::Illegal(IllegalReason::InvalidArg(msg))) => assert_eq!(msg, "message"),
        _ => panic!("wrong"),
    }
}

impl Value {
    /// Returns self is `Integral(v)` returns `Some(v)`, otherwise `None`.
    pub fn int(self) -> Option<u64> {
        match self {
            Value::Integral(v) => Some(v),
            _ => None,
        }
    }

    /// Returns self is `Floating(v)` returns `Some(v)`, otherwise `None`.
    pub fn float(self) -> Option<f64> {
        match self {
            Value::Floating(v) => Some(v),
            _ => None,
        }
    }
}

impl SymbolTable {
    /// Constructs an empty symbol table.
    pub fn new() -> Self {
        Default::default()
    }

    /// Checks if a symbol with the given name has already been defined.
    pub fn is_defined(&self, symbol: &str) -> bool {
        self.symbols.contains_key(symbol)
    }
    /// Introduces a new symbol.
    /// If not already defined, defines it and returns `Ok(())`.
    /// Otherwise, returns `Err(symbol)`.
    pub fn define(&mut self, symbol: String, value: Expr) -> Result<(), String> {
        if !self.is_defined(&symbol) {
            self.symbols.insert(symbol, value);
            Ok(())
        }
        else {
            Err(symbol)
        }
    }

    /// Gets the value of the given symbol if defined.
    pub fn get(&self, symbol: &str) -> Option<&Expr> {
        self.symbols.get(symbol)
    }

    /// Checks if the symbol table is empty.
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }
    /// Undefines all symbols, effectively restoring the newly-constructed state.
    /// This is meant to support resource reuse, and should not be used to remove or modify defined symbols.
    pub fn clear(&mut self) {
        self.symbols.clear();
    }
    /// Gets the number of defined symbols.
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Iterates over the defined symbols and their values.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Expr)> {
        self.symbols.iter()
    }
}
#[test]
fn test_symbol_table() {
    let mut s = SymbolTable::default();
    assert!(!s.is_defined("foo"));
    assert!(!s.is_defined("bar"));
    s.define("foo".to_string(), ExprData::Ident("bar".to_string()).into()).unwrap();
    assert!(s.is_defined("foo"));
    assert!(!s.is_defined("bar"));
    assert_eq!(s.define("foo".to_string(), ExprData::Ident("bar".to_string()).into()).unwrap_err(), "foo");
}

impl Uneval {
    fn eval<'a>(&'a self, symbols: &'a SymbolTable) -> Result<Value, EvalError> {
        fn binary_op<'a, II, FF>(left: &'a Option<Box<Expr>>, right: &'a Option<Box<Expr>>, symbols: &'a SymbolTable, ii: II, ff: FF) -> Result<Value, EvalError>
        where II: FnOnce(u64, u64) -> Result<Value, EvalError>, FF: FnOnce(f64, f64) -> Result<Value, EvalError>
        {
            let left = left.as_ref().unwrap().eval(symbols);
            let right = right.as_ref().unwrap().eval(symbols);
            all_legal(&[&left, &right])?; // if either was illegal, handle that first
            match left? {
                Value::Integral(a) => match right? {
                    Value::Integral(b) => ii(a, b),
                    Value::Floating(_) => Err(EvalError::Illegal(IllegalReason::MixIntFloat)),
                }
                Value::Floating(a) => match right? {
                    Value::Integral(_) => Err(EvalError::Illegal(IllegalReason::MixIntFloat)),
                    Value::Floating(b) => ff(a, b),
                }
            }
        }
        macro_rules! binary_op {
            ($ii:expr, $ff:expr) => {
                binary_op(&self.left, &self.right, symbols, $ii, $ff)
            }
        }

        fn unary_op<'a, I, F>(left: &'a Option<Box<Expr>>, right: &'a Option<Box<Expr>>, symbols: &'a SymbolTable, i: I, f: F) -> Result<Value, EvalError>
        where I: FnOnce(u64) -> Result<Value, EvalError>, F: FnOnce(f64) -> Result<Value, EvalError>
        {
            let left = left.as_ref().unwrap().eval(symbols);
            assert!(right.is_none()); // there should be no right operand
            match left? {
                Value::Integral(a) => i(a),
                Value::Floating(a) => f(a),
            }
        }
        macro_rules! unary_op {
            ($i:expr, $f:expr) => {
                unary_op(&self.left, &self.right, symbols, $i, $f)
            }
        }

        match self.op {
            OP::Invalid => panic!("invalid op encountered in expr"),
            OP::Mul => binary_op!(
                |a, b| Ok(Value::Integral(a.wrapping_mul(b))),
                |a, b| Ok(Value::Floating(a * b))
            ),
            OP::SDiv => binary_op!(
                |a, b| if b != 0 { Ok(Value::Integral((a as i64 / b as i64) as u64)) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) },
                |a, b| Ok(Value::Floating(a / b))
            ),
            OP::SMod => binary_op!(
                |a, b| if b != 0 { Ok(Value::Integral((a as i64 % b as i64) as u64)) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) },
                |a, b| Ok(Value::Floating(a % b))
            ),
            OP::UDiv => binary_op!(
                |a, b| if b != 0 { Ok(Value::Integral(a / b)) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) },
                |_, _| Err(EvalError::Illegal(IllegalReason::UnsignedFloat))
            ),
            OP::UMod => binary_op!(
                |a, b| if b != 0 { Ok(Value::Integral(a % b)) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) },
                |_, _| Err(EvalError::Illegal(IllegalReason::UnsignedFloat))
            ),
            OP::Add => binary_op!(
                |a, b| Ok(Value::Integral(a.wrapping_add(b))),
                |a, b| Ok(Value::Floating(a + b))
            ),
            OP::Sub => binary_op!(
                |a, b| Ok(Value::Integral(a.wrapping_sub(b))),
                |a, b| Ok(Value::Floating(a - b))
            ),
            OP::SHL => binary_op!(
                |a, b| Ok(Value::Integral(if b < 64 { a << b } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::SHR => binary_op!(
                |a, b| Ok(Value::Integral(if b < 64 { a >> b } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::SAR => binary_op!(
                |a, b| Ok(Value::Integral(if b < 64 { (a as i64 >> b) as u64 } else if a as i64 >= 0 { 0 } else { u64::MAX })),
                |_, _| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::SLess => binary_op!(
                |a, b| Ok(Value::Integral(if (a as i64) < (b as i64) { 1 } else { 0 })),
                |a, b| Ok(Value::Integral(if a < b { 1 } else { 0 }))
            ),
            OP::SLessE => binary_op!(
                |a, b| Ok(Value::Integral(if (a as i64) <= (b as i64) { 1 } else { 0 })),
                |a, b| Ok(Value::Integral(if a <= b { 1 } else { 0 }))
            ),
            OP::SGreat => binary_op!(
                |a, b| Ok(Value::Integral(if (a as i64) > (b as i64) { 1 } else { 0 })),
                |a, b| Ok(Value::Integral(if a > b { 1 } else { 0 }))
            ),
            OP::SGreatE => binary_op!(
                |a, b| Ok(Value::Integral(if (a as i64) >= (b as i64) { 1 } else { 0 })),
                |a, b| Ok(Value::Integral(if a >= b { 1 } else { 0 }))
            ),
            OP::ULess => binary_op!(
                |a, b| Ok(Value::Integral(if a < b { 1 } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::UnsignedFloat))
            ),
            OP::ULessE => binary_op!(
                |a, b| Ok(Value::Integral(if a <= b { 1 } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::UnsignedFloat))
            ),
            OP::UGreat => binary_op!(
                |a, b| Ok(Value::Integral(if a > b { 1 } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::UnsignedFloat))
            ),
            OP::UGreatE => binary_op!(
                |a, b| Ok(Value::Integral(if a >= b { 1 } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::UnsignedFloat))
            ),
            OP::Eq => binary_op!(
                |a, b| Ok(Value::Integral(if a == b { 1 } else { 0 })),
                |a, b| Ok(Value::Integral(if a == b { 1 } else { 0 }))
            ),
            OP::Neq => binary_op!(
                |a, b| Ok(Value::Integral(if a != b { 1 } else { 0 })),
                |a, b| Ok(Value::Integral(if a != b { 1 } else { 0 }))
            ),
            OP::BitAnd => binary_op!(
                |a, b| Ok(Value::Integral(a & b)),
                |_, _| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::BitXor => binary_op!(
                |a, b| Ok(Value::Integral(a ^ b)),
                |_, _| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::BitOr => binary_op!(
                |a, b| Ok(Value::Integral(a | b)),
                |_, _| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::LogAnd => binary_op!(
                |a, b| Ok(Value::Integral(if a != 0 && b != 0 { 1 } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::TruthyFloat))
            ),
            OP::LogOr => binary_op!(
                |a, b| Ok(Value::Integral(if a != 0 || b != 0 { 1 } else { 0 })),
                |_, _| Err(EvalError::Illegal(IllegalReason::TruthyFloat))
            ),
            OP::Neg => unary_op!(
                |a| Ok(Value::Integral((-(a as i64)) as u64)),
                |a| Ok(Value::Floating(-a))
            ),
            OP::BitNot => unary_op!(
                |a| Ok(Value::Integral(!a)),
                |_| Err(EvalError::Illegal(IllegalReason::BitwiseFloat))
            ),
            OP::LogNot => unary_op!(
                |a| Ok(Value::Integral(if a != 0 { 1 } else { 0 })),
                |_| Err(EvalError::Illegal(IllegalReason::TruthyFloat))
            ),
            OP::Int => unary_op!(
                |a| Ok(Value::Integral(a)), // int -> int is pass-through
                |a| Ok(Value::Integral(a as i64 as u64))
            ),
            OP::Float => unary_op!(
                |a| Ok(Value::Floating(a as i64 as f64)),
                |a| Ok(Value::Floating(a)) // float -> float is pass-through
            ),
            OP::Floor => unary_op!(
                |a| Ok(Value::Integral(a)), // rounding int is pass-through
                |a| Ok(Value::Floating(a.floor()))
            ),
            OP::Ceil => unary_op!(
                |a| Ok(Value::Integral(a)), // rounding int is pass-through
                |a| Ok(Value::Floating(a.ceil()))
            ),
            OP::Round => unary_op!(
                |a| Ok(Value::Integral(a)), // rounding int is pass-through
                |a| Ok(Value::Floating(a.round()))
            ),
            OP::Trunc => unary_op!(
                |a| Ok(Value::Integral(a)), // rounding int is pass-through
                |a| Ok(Value::Floating(a.trunc()))
            ),
            OP::Repr64 => unary_op!(
                |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use REPR64 on int"))),
                |a| Ok(Value::Integral(a.to_bits()))
            ),
            OP::Repr32 => unary_op!(
                |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use REPR32 on int"))),
                |a| Ok(Value::Integral((a as f32).to_bits() as u64))
            ),
            OP::Float64 => unary_op!(
                |a| Ok(Value::Floating(f64::from_bits(a))),
                |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use FLOAT64 on float")))
            ),
            OP::Float32 => unary_op!(
                |a| if a >> 32 == 0 { Ok(Value::Floating(f32::from_bits(a as u32) as f64)) } else { Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use FLOAT32 on a 64-bit value"))) },
                |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use FLOAT32 on float")))
            ),
            OP::Prec64 => unary_op!(
                |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use PREC64 on int"))),
                |a| Ok(Value::Floating(a)) // since we store internally as f64 this is pass-through
            ),
            OP::Prec32 => unary_op!(
                |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use PREC32 on int"))),
                |a| {
                    let bits = a.to_bits();
                    let mut res = bits & 0xffffffffe0000000;         // initially, just chop off the extra precision bits
                    if bits & 0x10000000 != 0 { res += 0x20000000; } // apply rounding if needed
                    Ok(Value::Floating(f64::from_bits(res)))
                }
            ),
            OP::Condition => {
                let cond = self.left.as_ref().unwrap().eval(symbols);
                let (r1, r2) = match &*self.right.as_ref().unwrap().data.borrow() {
                    ExprData::Uneval(Uneval { op: OP::Pair, left, right }) => (left.as_ref().unwrap().eval(symbols), right.as_ref().unwrap().eval(symbols)),
                    _ => panic!("encountered ill-formed ternary conditional in expr"),
                };
                all_legal(&[&cond, &r1, &r2])?; // if any were illegal, handle that first
                match cond? {
                    Value::Integral(cond) => if cond != 0 { r1 } else { r2 },
                    Value::Floating(_) => Err(EvalError::Illegal(IllegalReason::TruthyFloat)),
                }
            }
            OP::Pair => panic!("encountered ill-formed ternary conditional in expr"),
        }
    }
}
#[test]
#[should_panic]
fn test_uneval_invalid() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Invalid, left: Some(Box::new(Expr::from(2))), right: Some(Box::new(Expr::from(44))) })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_incomplete_ternary() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Condition, left: Some(Box::new(Expr::from(2))), right: Some(Box::new(Expr::from(44))) })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_dangling_pair() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Pair, left: Some(Box::new(Expr::from(2))), right: Some(Box::new(Expr::from(44))) })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_binary_1() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Add, left: None, right: Some(Box::new(Expr::from(44))) })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_binary_2() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Add, left: Some(Box::new(Expr::from(2))), right: None })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_binary_3() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Add, left: None, right: None })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_extra_unary() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Neg, left: Some(Box::new(Expr::from(2))), right: Some(Box::new(Expr::from(3))) })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_unary_1() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Neg, left: None, right: None })).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_unary_2() {
    let _ = Expr::from(ExprData::Uneval(Uneval { op: OP::Neg, left: None, right: Some(Box::new(Expr::from(3))) })).eval(&Default::default());
}
#[test]
fn test_uneval_eval() {
    let s = SymbolTable::default();
    macro_rules! make_expr {
        ($op:expr, $left:expr, $right:expr) => {
            Expr::from(($op, ExprData::from($left), ExprData::from($right)))
        }
    }

    // this is not exhaustive by any means.
    // more thorough testing will be done indirectly by testing the assembler.

    assert_eq!(make_expr!(OP::Mul, (4i64) as u64, (6i64) as u64).eval(&s).unwrap().int().unwrap(), (24i64) as u64);
    assert_eq!(make_expr!(OP::Mul, (-4i64) as u64, (6i64) as u64).eval(&s).unwrap().int().unwrap(), (-24i64) as u64);
    assert_eq!(make_expr!(OP::Mul, (4i64) as u64, (-6i64) as u64).eval(&s).unwrap().int().unwrap(), (-24i64) as u64);
    assert_eq!(make_expr!(OP::Mul, (-4i64) as u64, (-6i64) as u64).eval(&s).unwrap().int().unwrap(), (24i64) as u64);

    assert_eq!(make_expr!(OP::SDiv, (57i64) as u64, (10i64) as u64).eval(&s).unwrap().int().unwrap(), (5i64) as u64);
    assert_eq!(make_expr!(OP::SDiv, (-57i64) as u64, (10i64) as u64).eval(&s).unwrap().int().unwrap(), (-5i64) as u64);
    assert_eq!(make_expr!(OP::SDiv, (57i64) as u64, (-10i64) as u64).eval(&s).unwrap().int().unwrap(), (-5i64) as u64);
    assert_eq!(make_expr!(OP::SDiv, (-57i64) as u64, (-10i64) as u64).eval(&s).unwrap().int().unwrap(), (5i64) as u64);
    assert!(matches!(make_expr!(OP::SDiv, (-57i64) as u64, (0i64) as u64).eval(&s).unwrap_err(), EvalError::Illegal(IllegalReason::DivideByZero)));

    assert_eq!(make_expr!(OP::SMod, (57i64) as u64, (10i64) as u64).eval(&s).unwrap().int().unwrap(), (7i64) as u64);
    assert_eq!(make_expr!(OP::SMod, (-57i64) as u64, (10i64) as u64).eval(&s).unwrap().int().unwrap(), (-7i64) as u64);
    assert_eq!(make_expr!(OP::SMod, (57i64) as u64, (-10i64) as u64).eval(&s).unwrap().int().unwrap(), (7i64) as u64);
    assert_eq!(make_expr!(OP::SMod, (-57i64) as u64, (-10i64) as u64).eval(&s).unwrap().int().unwrap(), (-7i64) as u64);
    assert!(matches!(make_expr!(OP::SMod, (-57i64) as u64, (0i64) as u64).eval(&s).unwrap_err(), EvalError::Illegal(IllegalReason::DivideByZero)));
}

impl Expr {
    fn eval_recursive<'a>(mut root: std::cell::RefMut<'a, ExprData>, symbols: &'a SymbolTable) -> Result<Value, EvalError> {
        // decide how to approach evaluation
        let res = match &*root {
            ExprData::Value(val) => Ok(*val),                            // if it's a value, just return it
            ExprData::Uneval(uneval) => uneval.eval(symbols),            // if it's an unevaluated expression, evaluate it
            ExprData::Ident(ident) => match symbols.symbols.get(ident) { // if it's an identifier, look it up
                None => Err(EvalError::UndefinedSymbol(ident.to_string())),
                Some(entry) => {
                    // attempt to borrow it mutably - we don't allow symbol table content references to escape this module, so failure means cyclic dependency
                    match entry.data.try_borrow_mut() {
                        Err(_) => Err(EvalError::Illegal(IllegalReason::CyclicDependency)),
                        Ok(expr) => Self::eval_recursive(expr, symbols),
                    }
                }
            }
        };
        // if we successfully evaluated it, collapse to just a value node
        if let Ok(val) = res {
            *root = ExprData::Value(val);
        }
        res
    }
    /// Attempts to evaluate the expression given a symbol table to use.
    /// Due to reasons discussed in the doc entry for `SymbolTable`, once an `Expr` has been evaluated with a given symbol table
    /// it should never be evaluated with any other symbol table.
    pub fn eval<'a>(&'a self, symbols: &'a SymbolTable) -> Result<Value, EvalError> {
        Self::eval_recursive(self.data.borrow_mut(), symbols)
    }
}
#[test]
fn test_catch_cyclic_dep() {
    let mut s = SymbolTable::new();
    s.define("foo".into(), ExprData::Ident("bar".into()).into()).unwrap();
    s.define("bar".into(), ExprData::Ident("foo".into()).into()).unwrap();

    assert!(matches!(s.get("foo").unwrap().eval(&s), Err(EvalError::Illegal(IllegalReason::CyclicDependency))));
    assert!(matches!(s.get("bar").unwrap().eval(&s), Err(EvalError::Illegal(IllegalReason::CyclicDependency))));

    s.define("solipsis".into(), ExprData::Ident("solipsis".into()).into()).unwrap();
    assert!(matches!(s.get("solipsis").unwrap().eval(&s), Err(EvalError::Illegal(IllegalReason::CyclicDependency))));

    s.define("piano".into(), (OP::Add, ExprData::Ident("piano".into()), Expr::from(1)).into()).unwrap();
    assert!(matches!(s.get("piano").unwrap().eval(&s), Err(EvalError::Illegal(IllegalReason::CyclicDependency))));
}
