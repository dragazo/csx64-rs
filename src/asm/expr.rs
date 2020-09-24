//! Everything needed to handle expression trees.
//! 
//! The important types are `Expr`, which represents an expression tree, and `SymbolTable`, which is the special collection type used for evaluation.

use std::hash::Hash;
use std::collections::HashMap;
use std::cell::{self, RefCell};
use std::io::{self, Read, Write};
use std::ops::Deref;
use std::fmt::{self, Debug};
use std::mem;
use std::borrow::Cow;

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
    Div, Mod,
    Add, Sub,

    SHL, SHR,

    Less, LessE, Great, GreatE,
    Equ, Neq,

    And, Or, Xor,

    // unary ops

    Neg, Not,
    
    // function-like operators

    // Int, UInt, Float,
    // Floor, Ceil, Round, Trunc,

    // Int, Float, // convert int <-> float
    // Floor, Ceil, Round, Trunc,

    // Repr64, Repr32,   // interpret float as IEEE-754 encoded int
    // Float64, Float32, // interpret IEEE-754 encoded int as float
    // Prec64, Prec32,   // explicit precision truncations

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
#[derive(Debug, Clone)]
pub enum Value {
    Logical(bool),
    Signed(i64),
    Unsigned(u64),
    Floating(f64),
    Binary(Vec<u8>),
}
impl BinaryWrite for Value {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            Value::Logical(v) => match v {
                false => 0u8,
                true => 1u8,
            }.bin_write(f),
            Value::Signed(v) => {
                2u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Unsigned(v) => {
                3u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Floating(v) => {
                4u8.bin_write(f)?;
                v.to_bits().bin_write(f)
            }
            Value::Binary(v) => {
                5u8.bin_write(f)?;
                v.bin_write(f)
            }
        }
    }
}
impl BinaryRead for Value {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Value> {
        match u8::bin_read(f)? {
            0 => Ok(Value::Logical(false)),
            1 => Ok(Value::Logical(true)),
            2 => Ok(Value::Signed(BinaryRead::bin_read(f)?)),
            3 => Ok(Value::Unsigned(BinaryRead::bin_read(f)?)),
            4 => Ok(Value::Floating(BinaryRead::bin_read(f)?)),
            5 => Ok(Value::Binary(BinaryRead::bin_read(f)?)),
            _ => Err(io::ErrorKind::InvalidData.into()),
        }
    }
}
impl From<bool> for Value {
    fn from(val: bool) -> Self {
        Value::Logical(val)
    }
}
impl From<i64> for Value {
    fn from(val: i64) -> Self {
        Value::Signed(val)
    }
}
impl From<u64> for Value {
    fn from(val: u64) -> Self {
        Value::Unsigned(val)
    }
}
impl From<f64> for Value {
    fn from(val: f64) -> Self {
        Value::Floating(val)
    }
}
impl From<Vec<u8>> for Value {
    fn from(val: Vec<u8>) -> Self {
        Value::Binary(val)
    }
}

impl Value {
    fn logical(self) -> Option<bool> {
        match self {
            Value::Logical(v) => Some(v),
            _ => None,
        }
    }
    fn signed(self) -> Option<i64> {
        match self {
            Value::Signed(v) => Some(v),
            _ => None,
        }
    }
    fn unsigned(self) -> Option<u64> {
        match self {
            Value::Unsigned(v) => Some(v),
            _ => None,
        }
    }
    fn floating(self) -> Option<f64> {
        match self {
            Value::Floating(v) => Some(v),
            _ => None,
        }
    }
    fn binary(self) -> Option<Vec<u8>> {
        match self {
            Value::Binary(v) => Some(v),
            _ => None,
        }
    }
}
pub trait ValueVariants<'a> {
    fn logical(self) -> Option<Cow<'a, bool>>;
    fn signed(self) -> Option<Cow<'a, i64>>;
    fn unsigned(self) -> Option<Cow<'a, u64>>;
    fn floating(self) -> Option<Cow<'a, f64>>;
    fn binary(self) -> Option<Cow<'a, [u8]>>;
}
impl<'a> ValueVariants<'a> for Cow<'a, Value> {
    fn logical(self) -> Option<Cow<'a, bool>> {
        match self {
            Cow::Owned(Value::Logical(v)) => Some(Cow::Owned(v)),
            Cow::Borrowed(Value::Logical(v)) => Some(Cow::Borrowed(v)),
            _ => None,
        }
    }
    fn signed(self) -> Option<Cow<'a, i64>> {
        match self {
            Cow::Owned(Value::Signed(v)) => Some(Cow::Owned(v)),
            Cow::Borrowed(Value::Signed(v)) => Some(Cow::Borrowed(v)),
            _ => None,
        }
    }
    fn unsigned(self) -> Option<Cow<'a, u64>> {
        match self {
            Cow::Owned(Value::Unsigned(v)) => Some(Cow::Owned(v)),
            Cow::Borrowed(Value::Unsigned(v)) => Some(Cow::Borrowed(v)),
            _ => None,
        }
    }
    fn floating(self) -> Option<Cow<'a, f64>> {
        match self {
            Cow::Owned(Value::Floating(v)) => Some(Cow::Owned(v)),
            Cow::Borrowed(Value::Floating(v)) => Some(Cow::Borrowed(v)),
            _ => None,
        }
    }
    fn binary(self) -> Option<Cow<'a, [u8]>> {
        match self {
            Cow::Owned(Value::Binary(v)) => Some(Cow::Owned(v)),
            Cow::Borrowed(Value::Binary(v)) => Some(Cow::Borrowed(v)),
            _ => None,
        }
    }
}

/// Holds the information needed to create an instance of `Expr`.
/// 
/// # Example
/// ```
/// # use csx64::asm::expr::*;
/// let ex: Expr = ExprData::Ident("foo".into()).into();
/// let ey: Expr = 12u64.into(); // thanks to convenience functions, ExprData::Value is even simpler
/// println!("{:?} {:?}", ex, ey);
/// ```
#[derive(Clone)]
pub enum ExprData {
    Value(Value),
    Ident(String),
    Uneval { op: OP, left: Option<Box<Expr>>, right: Option<Box<Expr>> },
}
impl BinaryWrite for ExprData {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            ExprData::Value(Value::Logical(false)) => 0xffu8.bin_write(f),
            ExprData::Value(Value::Logical(true)) => 0xfeu8.bin_write(f),
            ExprData::Value(Value::Signed(value)) => {
                0xfdu8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Unsigned(value)) => {
                0xfcu8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Floating(value)) => {
                0xfbu8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Binary(value)) => {
                0xfau8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Ident(ident) => {
                0xf9u8.bin_write(f)?;
                ident.bin_write(f)
            }
            ExprData::Uneval { op, left, right } => {
                match right {
                    None => {
                        (*op as u8).bin_write(f)?;
                        left.as_ref().expect("left branch of expr cannot be empty").bin_write(f)
                    }
                    Some(right) => {
                        (0x80 | *op as u8).bin_write(f)?;
                        left.as_ref().expect("left branch of expr cannot be empty").bin_write(f)?;
                        right.bin_write(f)
                    }
                }
            }
        }
    }
}
impl BinaryRead for ExprData {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<ExprData> {
        match u8::bin_read(f)? {
            0xff => Ok(false.into()),
            0xfe => Ok(true.into()),
            0xfd => Ok(Value::Signed(BinaryRead::bin_read(f)?).into()),
            0xfc => Ok(Value::Unsigned(BinaryRead::bin_read(f)?).into()),
            0xfb => Ok(Value::Floating(BinaryRead::bin_read(f)?).into()),
            0xfa => Ok(Value::Binary(BinaryRead::bin_read(f)?).into()),
            0xf9 => Ok(ExprData::Ident(String::bin_read(f)?)),
            x => match OP::from_u8(x & 0x7f) {
                None => Err(io::ErrorKind::InvalidData.into()),
                Some(op) => {
                    let left = Some(BinaryRead::bin_read(f)?);
                    let right = if x >= 0x80 { Some(BinaryRead::bin_read(f)?) } else { None };
                    Ok(ExprData::Uneval { op, left, right })
                }
            }
        }
    }
}
impl fmt::Debug for ExprData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExprData::Value(val) => write!(f, "{:?}", val),
            ExprData::Uneval { op, left, right } => write!(f, "{:?}({:?}, {:?})", op, left, right),
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
        ExprData::Uneval { op: vals.0, left: Some(Box::new(vals.1.into())), right: Some(Box::new(vals.2.into())) }
    }
}
/// Convenience for creating instances of `ExprData::Uneval` for unary ops.
impl<T> From<(OP, T)> for ExprData where Expr: From<T> {
    fn from(vals: (OP, T)) -> Self {
        ExprData::Uneval { op: vals.0, left: Some(Box::new(vals.1.into())), right: None }
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
    pub(super) data: RefCell<ExprData>,
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
/// symbols.define("foo".into(), 2u64.into()).unwrap();
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
    MixedTypes,
    CyclicDependency,

    DivideByZero,
    UnsignedNegative,

    ArithmeticBool,
    ShiftBool,
    OrderedBool,

    LogicalInt,

    ArithmeticString,
    ShiftString,
    LogicalString,

    ShiftFloat,
    LogicalFloat,
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

fn all_legal(res: &[&Result<ValueRef, EvalError>]) -> Result<(), EvalError> {
    for &x in res.iter() {
        if let Err(EvalError::Illegal(reason)) = x {
            return Err(EvalError::Illegal(*reason));
        }
    }
    Ok(())
}
#[test]
fn test_all_legal() {
    assert!(all_legal(&[&Ok(Expr::from(34u64).value_ref()), &Ok(Expr::from(3.42).value_ref())]).is_ok());
    assert!(all_legal(&[&Ok(Expr::from(54u64).value_ref()), &Err(EvalError::UndefinedSymbol("heloo".into()))]).is_ok());
    assert!(all_legal(&[&Err(EvalError::UndefinedSymbol("heloo".into())), &Err(EvalError::UndefinedSymbol("heloo".into()))]).is_ok());
    match all_legal(&[&Err(EvalError::Illegal(IllegalReason::LogicalInt)), &Err(EvalError::UndefinedSymbol("heloo".into()))]) {
        Err(EvalError::Illegal(IllegalReason::LogicalInt)) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Err(EvalError::UndefinedSymbol("heloo".into())), &Err(EvalError::Illegal(IllegalReason::MixedTypes))]) {
        Err(EvalError::Illegal(IllegalReason::MixedTypes)) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Ok(Expr::from(463i64).value_ref()), &Err(EvalError::Illegal(IllegalReason::ArithmeticString))]) {
        Err(EvalError::Illegal(IllegalReason::ArithmeticString)) => (),
        _ => panic!("wrong"),
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
    s.define("foo".into(), ExprData::Ident("bar".into()).into()).unwrap();
    assert!(s.is_defined("foo"));
    assert!(!s.is_defined("bar"));
    assert_eq!(s.define("foo".into(), ExprData::Ident("bar".into()).into()).unwrap_err(), "foo");
}

enum Ownership<'a> {
    Mine, // denotes that i own the value (i.e. from ExprData::Value)
    Theirs { my_handle: cell::RefMut<'a, ExprData> }, // denotes that i don't own the value (e.g. from ExprData::Ident)
}
pub(super) struct ValueRef<'a> {
    handle: cell::RefMut<'a, ExprData>, // handle that holds the value we refer to
    ownership: Ownership<'a>, // our type of ownership of the value
}
impl<'a> Deref for ValueRef<'a> {
    type Target = Value;
    fn deref(&self) -> &Value {
        match &*self.handle {
            ExprData::Value(val) => val,
            _ => unreachable!(),
        }
    }
}
impl<'a> ValueRef<'a> {
    fn mine(handle: cell::RefMut<'a, ExprData>) -> Self {
        Self { ownership: Ownership::Mine, handle }
    }
    fn theirs(my_handle: cell::RefMut<'a, ExprData>, their_handle: cell::RefMut<'a, ExprData>) -> Self {
        Self { ownership: Ownership::Theirs { my_handle }, handle: their_handle }
    }

    /// Returns a mutable reference to my value - if I don't own it, clones theirs into mine and returns a reference to that.
    fn to_mut(&mut self) -> &mut Value {
        // transition to owning state - if we weren't owning before, assign a cloned value to our handle and repoint to ourselves
        if let Ownership::Theirs { mut my_handle } = mem::replace(&mut self.ownership, Ownership::Mine) {
            *my_handle = ExprData::Value((**self).clone());
            self.handle = my_handle;
        }
        match &mut *self.handle {
            ExprData::Value(val) => val,
            _ => unreachable!(),
        }
    }
    /// Either takes my value or clones theirs.
    pub(super) fn take_or_clone(&mut self) -> Value {
        mem::replace(self.to_mut(), Value::Logical(false)) // take the value and leave some valid replacement that's non-allocating
    }
    /// Either takes my value or borrows theirs
    pub(super) fn take_or_borrow(&mut self) -> Cow<Value> {
        match self.ownership {
            Ownership::Mine => Cow::Owned(self.take_or_clone()),
            Ownership::Theirs { my_handle: _ } => Cow::Borrowed(&**self),
        }
    }
}
impl<'a> Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self.deref())
    }
}

impl Expr {
    fn eval_recursive<'a>(mut root: cell::RefMut<'a, ExprData>, symbols: &'a SymbolTable) -> Result<ValueRef<'a>, EvalError> {
        // decide how to approach evaluation
        let res: Value = match &*root {
            ExprData::Value(_) => return Ok(ValueRef::mine(root)), // if we're a value node, we already have the value - skip caching
            ExprData::Ident(ident) => match symbols.symbols.get(ident) { // if it's an identifier, look it up
                None => return Err(EvalError::UndefinedSymbol(ident.clone())),
                Some(entry) => match entry.data.try_borrow_mut() { // attempt to borrow it mutably - we don't allow symbol table content references to escape this module, so failure means cyclic dependency
                    Err(_) => return Err(EvalError::Illegal(IllegalReason::CyclicDependency)),
                    Ok(expr) => return Ok(ValueRef::theirs(root, Self::eval_recursive(expr, symbols)?.handle)),
                }
            }
            ExprData::Uneval { op, left, right } => { // if it's an unevaluated expression, evaluate it
                fn binary_op<'a, LL, SS, UU, FF, BB>(left: &'a Option<Box<Expr>>, right: &'a Option<Box<Expr>>, symbols: &'a SymbolTable, ll: LL, ss: SS, uu: UU, ff: FF, bb: BB) -> Result<Value, EvalError>
                where LL: FnOnce(bool, bool) -> Result<Value, EvalError>, SS: FnOnce(i64, i64) -> Result<Value, EvalError>, UU: FnOnce(u64, u64) -> Result<Value, EvalError>,
                    FF: FnOnce(f64, f64) -> Result<Value, EvalError>, BB: FnOnce(Vec<u8>, Vec<u8>) -> Result<Value, EvalError>
                {
                    let left = left.as_ref().unwrap().eval(symbols);
                    let right = right.as_ref().unwrap().eval(symbols);
                    all_legal(&[&left, &right])?; // if either was illegal, handle that first
                    let (mut left, mut right) = (left?, right?);
                    match left.take_or_clone() {
                        Value::Logical(a) => match right.take_or_clone() {
                            Value::Logical(b) => ll(a, b),
                            _ => Err(EvalError::Illegal(IllegalReason::MixedTypes)),
                        }
                        Value::Signed(a) => match right.take_or_clone() {
                            Value::Signed(b) => ss(a, b),
                            _ => Err(EvalError::Illegal(IllegalReason::MixedTypes)),
                        }
                        Value::Unsigned(a) => match right.take_or_clone() {
                            Value::Unsigned(b) => uu(a, b),
                            _ => Err(EvalError::Illegal(IllegalReason::MixedTypes)),
                        }
                        Value::Floating(a) => match right.take_or_clone() {
                            Value::Floating(b) => ff(a, b),
                            _ => Err(EvalError::Illegal(IllegalReason::MixedTypes)),
                        }
                        Value::Binary(a) => match right.take_or_clone() {
                            Value::Binary(b) => bb(a, b),
                            _ => Err(EvalError::Illegal(IllegalReason::MixedTypes)),
                        }
                    }
                }
                macro_rules! binary_op {
                    ($ll:expr; $ss:expr; $uu:expr; $ff:expr; $bb:expr;) => {
                        binary_op(&left, &right, symbols, $ll, $ss, $uu, $ff, $bb)?
                    }
                }
        
                fn unary_op<'a, L, S, U, F, B>(left: &'a Option<Box<Expr>>, right: &'a Option<Box<Expr>>, symbols: &'a SymbolTable, l: L, s: S, u: U, f: F, b: B) -> Result<Value, EvalError>
                where L: FnOnce(bool) -> Result<Value, EvalError>, S: FnOnce(i64) -> Result<Value, EvalError>, U: FnOnce(u64) -> Result<Value, EvalError>,
                    F: FnOnce(f64) -> Result<Value, EvalError>, B: FnOnce(Vec<u8>) -> Result<Value, EvalError>
                {
                    let left = left.as_ref().unwrap().eval(symbols);
                    assert!(right.is_none()); // there should be no right operand
                    match left?.take_or_clone() {
                        Value::Logical(a) => l(a),
                        Value::Signed(a) => s(a),
                        Value::Unsigned(a) => u(a),
                        Value::Floating(a) => f(a),
                        Value::Binary(a) => b(a),
                    }
                }
                macro_rules! unary_op {
                    ($l:expr; $s:expr; $u:expr; $f:expr; $b:expr;) => {
                        unary_op(&left, &right, symbols, $l, $s, $u, $f, $b)?
                    }
                }

                match op {
                    OP::Invalid => panic!("invalid op encountered in expr"),
                    OP::Mul => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticBool));
                        |a, b| Ok(a.wrapping_mul(b).into());
                        |a, b| Ok(a.wrapping_mul(b).into());
                        |a, b| Ok((a * b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticString));
                    },
                    OP::Div => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticBool));
                        |a, b| if b != 0 { Ok((a / b).into()) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) };
                        |a, b| if b != 0 { Ok((a / b).into()) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) };
                        |a, b| Ok((a / b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticString));
                    },
                    OP::Mod => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticBool));
                        |a, b| if b != 0 { Ok((a % b).into()) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) };
                        |a, b| if b != 0 { Ok((a % b).into()) } else { Err(EvalError::Illegal(IllegalReason::DivideByZero)) };
                        |a, b| Ok((a % b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticString));
                    },
                    OP::Add => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticBool));
                        |a, b| Ok(a.wrapping_add(b).into());
                        |a, b| Ok(a.wrapping_add(b).into());
                        |a, b| Ok((a + b).into());
                        |mut a, mut b| { a.append(&mut b); Ok(Value::Binary(a)) };
                    },
                    OP::Sub => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticBool));
                        |a, b| Ok(a.wrapping_sub(b).into());
                        |a, b| Ok(a.wrapping_sub(b).into());
                        |a, b| Ok((a - b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::ArithmeticString));
                    },
                    OP::SHL => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ShiftBool));
                        |a, b| Ok(if b < 64 { a << b } else { 0 }.into());
                        |a, b| Ok(if b < 64 { a << b } else { 0 }.into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::ShiftFloat));
                        |_, _| Err(EvalError::Illegal(IllegalReason::ShiftString));
                    },
                    OP::SHR => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::ShiftBool));
                        |a, b| Ok(if b < 64 { a >> b } else { 0 }.into());
                        |a, b| Ok(if b < 64 { a >> b } else { 0 }.into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::ShiftFloat));
                        |_, _| Err(EvalError::Illegal(IllegalReason::ShiftString));
                    },
                    OP::Less => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::OrderedBool));
                        |a, b| Ok((a < b).into());
                        |a, b| Ok((a < b).into());
                        |a, b| Ok((a < b).into());
                        |a, b| Ok((a < b).into());
                    },
                    OP::LessE => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::OrderedBool));
                        |a, b| Ok((a <= b).into());
                        |a, b| Ok((a <= b).into());
                        |a, b| Ok((a <= b).into());
                        |a, b| Ok((a <= b).into());
                    },
                    OP::Great => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::OrderedBool));
                        |a, b| Ok((a > b).into());
                        |a, b| Ok((a > b).into());
                        |a, b| Ok((a > b).into());
                        |a, b| Ok((a > b).into());
                    },
                    OP::GreatE => binary_op! {
                        |_, _| Err(EvalError::Illegal(IllegalReason::OrderedBool));
                        |a, b| Ok((a >= b).into());
                        |a, b| Ok((a >= b).into());
                        |a, b| Ok((a >= b).into());
                        |a, b| Ok((a >= b).into());
                    },
                    OP::Equ => binary_op! {
                        |a, b| Ok((a == b).into());
                        |a, b| Ok((a == b).into());
                        |a, b| Ok((a == b).into());
                        |a, b| Ok((a == b).into());
                        |a, b| Ok((a == b).into());
                    },
                    OP::Neq => binary_op! {
                        |a, b| Ok((a != b).into());
                        |a, b| Ok((a != b).into());
                        |a, b| Ok((a != b).into());
                        |a, b| Ok((a != b).into());
                        |a, b| Ok((a != b).into());
                    },
                    OP::And => binary_op! {
                        |a, b| Ok((a && b).into());
                        |a, b| Ok((a & b).into());
                        |a, b| Ok((a & b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::LogicalFloat));
                        |_, _| Err(EvalError::Illegal(IllegalReason::LogicalString));
                    },
                    OP::Or => binary_op! {
                        |a, b| Ok((a || b).into());
                        |a, b| Ok((a | b).into());
                        |a, b| Ok((a | b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::LogicalFloat));
                        |_, _| Err(EvalError::Illegal(IllegalReason::LogicalString));
                    },
                    OP::Xor => binary_op! {
                        |a, b| Ok((a ^ b).into());
                        |a, b| Ok((a ^ b).into());
                        |a, b| Ok((a ^ b).into());
                        |_, _| Err(EvalError::Illegal(IllegalReason::LogicalFloat));
                        |_, _| Err(EvalError::Illegal(IllegalReason::LogicalString));
                    },
                    OP::Neg => unary_op! {
                        |_| Err(EvalError::Illegal(IllegalReason::ArithmeticBool));
                        |a| Ok((-a).into());
                        |_| Err(EvalError::Illegal(IllegalReason::UnsignedNegative));
                        |a| Ok((-a).into());
                        |_| Err(EvalError::Illegal(IllegalReason::ArithmeticString));
                    },
                    OP::Not => unary_op! {
                        |a| Ok((!a).into());
                        |a| Ok((!a).into());
                        |a| Ok((!a).into());
                        |_| Err(EvalError::Illegal(IllegalReason::LogicalFloat));
                        |_| Err(EvalError::Illegal(IllegalReason::LogicalString));
                    },
                    // OP::Int => unary_op! {
                    //     |a| Ok(if a { 1i64 } else { 0i64 }.into());
                    //     |a| Ok(a.into());
                    //     |a| Ok((a as i64).into());
                    //     |a| Ok((a as i64).into());
                    //     |_| Err(EvalError::Illegal(IllegalReason::StringParsing));
                    // },
                    // OP::UInt => unary_op! {
                    //     |a| Ok(if a { 1u64 } else { 0u64 }.into());
                    //     |a| Ok((a as u64).into());
                    //     |a| Ok(a.into());
                    //     |a| Ok((a as u64).into());
                    //     |_| Err(EvalError::Illegal(IllegalReason::StringParsing));
                    // },
                    // OP::Float => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| Ok(Value::Floating(a as i64 as f64));
                    //     |a| Ok(Value::Floating(a)); // float -> float is pass-through
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Floor => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| Ok(Value::Integral(a)); // rounding int is pass-through
                    //     |a| Ok(Value::Floating(a.floor()));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Ceil => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| Ok(Value::Integral(a)); // rounding int is pass-through
                    //     |a| Ok(Value::Floating(a.ceil()));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Round => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| Ok(Value::Integral(a)); // rounding int is pass-through
                    //     |a| Ok(Value::Floating(a.round()));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Trunc => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| Ok(Value::Integral(a)); // rounding int is pass-through
                    //     |a| Ok(Value::Floating(a.trunc()));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Repr64 => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use REPR64 on int")));
                    //     |a| Ok(Value::Integral(a.to_bits()));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Repr32 => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use REPR32 on int")));
                    //     |a| Ok(Value::Integral((a as f32).to_bits() as u64));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Float64 => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| Ok(Value::Floating(f64::from_bits(a)));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use FLOAT64 on float")));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Float32 => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |a| if a >> 32 == 0 { Ok(Value::Floating(f32::from_bits(a as u32) as f64)) }
                    //         else { Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use FLOAT32 on a 64-bit value"))) };
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use FLOAT32 on float")));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Prec64 => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use PREC64 on int")));
                    //     |a| Ok(Value::Floating(a)); // since we store internally as f64 this is pass-through
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    // OP::Prec32 => unary_op! {
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidBoolOp));
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidArg("attempt to use PREC32 on int")));
                    //     |a| {
                    //         let bits = a.to_bits();
                    //         let mut res = bits & 0xffffffffe0000000;         // initially, just chop off the extra precision bits
                    //         if bits & 0x10000000 != 0 { res += 0x20000000; } // apply rounding if needed
                    //         Ok(Value::Floating(f64::from_bits(res)))
                    //     };
                    //     |_| Err(EvalError::Illegal(IllegalReason::InvalidStringOp));
                    // },
                    OP::Condition => {
                        let cond = left.as_ref().unwrap().eval(symbols);
                        let val = match &*right.as_ref().unwrap().data.borrow() {
                            ExprData::Uneval { op: OP::Pair, left, right } => {
                                let r1 = left.as_ref().unwrap().eval(symbols);
                                let r2 = right.as_ref().unwrap().eval(symbols);
                                all_legal(&[&cond, &r1, &r2])?; // if any were illegal, handle that first

                                let (mut cond, r1, r2) = (cond?, r1?, r2?);
                                let cond = match cond.take_or_clone() { // we can take the values because we're guaranteed to own them (not from different symbol in table)
                                    Value::Logical(v) => v,
                                    Value::Signed(_) => return Err(EvalError::Illegal(IllegalReason::LogicalInt)),
                                    Value::Unsigned(_) => return Err(EvalError::Illegal(IllegalReason::LogicalInt)),
                                    Value::Floating(_) => return Err(EvalError::Illegal(IllegalReason::LogicalFloat)),
                                    Value::Binary(_) => return Err(EvalError::Illegal(IllegalReason::LogicalString)),
                                };
                                if cond { r1 } else { r2 } .take_or_clone()
                            }
                            _ => panic!("encountered ill-formed ternary conditional in expr"),
                        };
                        
                        *root = ExprData::Value(val);
                        return Ok(ValueRef::mine(root)); // we now have a (cached) value - just pass that back directly
                    }
                    OP::Pair => panic!("encountered ill-formed ternary conditional in expr"),
                }
            }
        };

        // we successfully evaluated it - collapse to just a value node
        *root = ExprData::Value(res);
        Ok(ValueRef::mine(root))
    }
    /// Attempts to evaluate the expression given a symbol table to use.
    /// Due to reasons discussed in the doc entry for `SymbolTable`, once an `Expr` has been evaluated with a given symbol table
    /// it should never be evaluated with any other symbol table.
    pub(super) fn eval<'a>(&'a self, symbols: &'a SymbolTable) -> Result<ValueRef<'a>, EvalError> {
        Self::eval_recursive(self.data.borrow_mut(), symbols)
    }

    #[cfg(test)]
    fn value_ref(&self) -> ValueRef {
        let handle = self.data.borrow_mut();
        match &*handle {
            ExprData::Value(_) => ValueRef::mine(handle),
            _ => unreachable!(),
        }
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

    s.define("piano".into(), (OP::Add, ExprData::Ident("piano".into()), Expr::from(1i64)).into()).unwrap();
    assert!(matches!(s.get("piano").unwrap().eval(&s), Err(EvalError::Illegal(IllegalReason::CyclicDependency))));
}

#[test]
#[should_panic]
fn test_uneval_invalid() {
    let _ = Expr::from((OP::Invalid, 2u64, 44u64)).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_incomplete_ternary() {
    let _ = Expr::from((OP::Condition, 2u64, 44u64)).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_dangling_pair() {
    let _ = Expr::from((OP::Pair, 2u64, 44u64)).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_binary_1() {
    let _ = Expr::from(ExprData::Uneval { op: OP::Add, left: None, right: Some(Box::new(44u64.into())) }).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_binary_2() {
    let _ = Expr::from(ExprData::Uneval { op: OP::Add, left: Some(Box::new(2u64.into())), right: None }).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_binary_3() {
    let _ = Expr::from(ExprData::Uneval { op: OP::Add, left: None, right: None }).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_extra_unary() {
    let _ = Expr::from(ExprData::Uneval { op: OP::Neg, left: Some(Box::new(2u64.into())), right: Some(Box::new(3u64.into())) }).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_unary_1() {
    let _ = Expr::from(ExprData::Uneval { op: OP::Neg, left: None, right: None }).eval(&Default::default());
}
#[test]
#[should_panic]
fn test_uneval_missing_unary_2() {
    let _ = Expr::from(ExprData::Uneval { op: OP::Neg, left: None, right: Some(Box::new(3u64.into())) }).eval(&Default::default());
}
#[test]
fn test_expr_eval() {
    let mut s = SymbolTable::default();
    macro_rules! make_expr {
        ($op:expr, $left:expr, $right:expr) => {
            Expr::from(($op, ExprData::from($left), ExprData::from($right)))
        }
    }

    // this is not exhaustive by any means.
    // more thorough testing will be done indirectly by testing the assembler.

    assert_eq!(make_expr!(OP::Mul, 4i64, 6i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 24i64);
    assert_eq!(make_expr!(OP::Mul, -4i64, 6i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), -24i64);
    assert_eq!(make_expr!(OP::Mul, 4i64, -6i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), -24i64);
    assert_eq!(make_expr!(OP::Mul, -4i64, -6i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 24i64);

    assert_eq!(make_expr!(OP::Div, 57i64, 10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 5i64);
    assert_eq!(make_expr!(OP::Div, -57i64, 10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), -5i64);
    assert_eq!(make_expr!(OP::Div, 57i64, -10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), -5i64);
    assert_eq!(make_expr!(OP::Div, -57i64, -10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 5i64);
    assert!(matches!(make_expr!(OP::Div, -57i64, 0i64).eval(&s).unwrap_err(), EvalError::Illegal(IllegalReason::DivideByZero)));

    assert_eq!(make_expr!(OP::Mod, 57i64, 10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 7i64);
    assert_eq!(make_expr!(OP::Mod, -57i64, 10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), -7i64);
    assert_eq!(make_expr!(OP::Mod, 57i64, -10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 7i64);
    assert_eq!(make_expr!(OP::Mod, -57i64, -10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), -7i64);
    assert!(matches!(make_expr!(OP::Mod, -57i64, 0i64).eval(&s).unwrap_err(), EvalError::Illegal(IllegalReason::DivideByZero)));

    // make sure that the new take() logic is safe when used on Ident (make sure it takes a copy, not the actual symbol value)
    s.define("foo".into(), 654i64.into()).unwrap();
    assert_eq!(Expr::from(ExprData::Ident("foo".into())).eval(&s).unwrap().take_or_clone().signed().unwrap(), 654);
    assert_eq!(Expr::from(ExprData::Ident("foo".into())).eval(&s).unwrap().take_or_clone().signed().unwrap(), 654); // do it twice - second time is the potential failure
    assert_eq!(make_expr!(OP::Add, ExprData::Ident("foo".into()), 10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 664);
    assert_eq!(make_expr!(OP::Add, ExprData::Ident("foo".into()), 10i64).eval(&s).unwrap().take_or_clone().signed().unwrap(), 664); // do it twice - second time is the potential failure

    s.define("msg".into(), "owo wats dis".as_bytes().to_owned().into()).unwrap();
    s.define("msg2".into(), "rawr xd".as_bytes().to_owned().into()).unwrap();
    assert_eq!(Expr::from(ExprData::Ident("msg".into())).eval(&s).unwrap().take_or_clone().binary().unwrap(), "owo wats dis".as_bytes());
    assert_eq!(Expr::from(ExprData::Ident("msg".into())).eval(&s).unwrap().take_or_clone().binary().unwrap(), "owo wats dis".as_bytes()); // do it twice - second time is the potential failure
    assert_eq!(make_expr!(OP::Add, ExprData::Ident("msg".into()), ExprData::Ident("msg2".into())).eval(&s).unwrap().take_or_clone().binary().unwrap(), "owo wats disrawr xd".as_bytes());
    assert_eq!(make_expr!(OP::Add, ExprData::Ident("msg".into()), ExprData::Ident("msg2".into())).eval(&s).unwrap().take_or_clone().binary().unwrap(), "owo wats disrawr xd".as_bytes()); // do it twice - second time is the potential failure
}
