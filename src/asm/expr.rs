//! Everything needed to handle expression trees.
//! 
//! The important types are `Expr`, which represents an expression tree, and `SymbolTable`, which is the special collection type used for evaluation.

use std::hash::Hash;
use std::collections::{HashSet, HashMap};
use std::cell::{self, RefCell};
use std::io::{self, Read, Write};
use std::ops::Deref;
use std::fmt::{self, Debug};
use std::cmp::Ordering;
use std::iter::FusedIterator;
use rug::{Integer, Float};

#[cfg(test)]
use std::io::Cursor;

use num_traits::FromPrimitive;

use crate::common::serialization::*;

/// Number of precision bits to use for floating point values.
/// This is strictly larger than fpu precision (64) so that we can have nigh-perfect end-results from expr after truncating to 64.
pub const FLOAT_PRECISION: u32 = 80;
/// Maximum number of significant bits to use for integer values.
/// Values exceeding this are hard errors.
/// This should at least be high enough to compute full products of u64 and i64.
pub const INT_PRECISION: u32 = 136;

/// The supported operations in an expr.
/// 
/// For safety, in nearly all contexts it is considered illegal to mix integral and floating-point values.
/// An important exception is the ternary conditional, which is allowed due to the fact that it can short circuit and is compile-time only.
#[derive(Debug, Clone, Copy, FromPrimitive, PartialOrd, Ord, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum OP {
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ValueType {
    Logical,
    Pointer,
    Character,
    Integer,
    Float,
    Binary,
}

#[derive(Debug, Clone)]
pub enum Value {
    Logical(bool),
    Pointer(u64),
    Character(char),
    Integer(Integer),
    Float(Float),
    Binary(Vec<u8>),
}
impl BinaryWrite for Value {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            Value::Logical(v) => match v {
                false => 0u8,
                true => 1u8,
            }.bin_write(f),
            Value::Pointer(v) => {
                2u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Character(v) => {
                3u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Integer(v) => {
                4u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Float(v) => {
                5u8.bin_write(f)?;
                v.bin_write(f)
            }
            Value::Binary(v) => {
                6u8.bin_write(f)?;
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
            2 => Ok(Value::Pointer(BinaryRead::bin_read(f)?)),
            3 => Ok(Value::Character(BinaryRead::bin_read(f)?)),
            4 => Ok(Value::Integer(BinaryRead::bin_read(f)?)),
            5 => Ok(Value::Float(BinaryRead::bin_read(f)?)),
            6 => Ok(Value::Binary(BinaryRead::bin_read(f)?)),
            _ => Err(io::ErrorKind::InvalidData.into()),
        }
    }
}
impl From<bool> for Value {
    fn from(val: bool) -> Self {
        Value::Logical(val)
    }
}
impl From<char> for Value {
    fn from(val: char) -> Self {
        Value::Character(val)
    }
}
impl From<Integer> for Value {
    fn from(val: Integer) -> Self {
        Value::Integer(val)
    }
}
impl From<Float> for Value {
    fn from(val: Float) -> Self {
        Value::Float(val)
    }
}
impl From<Vec<u8>> for Value {
    fn from(val: Vec<u8>) -> Self {
        Value::Binary(val)
    }
}

macro_rules! value_from_int_impl {
    ($($t:ty),*) => {$(
        impl From<$t> for Value {
            fn from(val: $t) -> Self {
                Value::Integer(val.into())
            }
        }
    )*}
}
value_from_int_impl! { u8, u16, u32, u64, i8, i16, i32, i64 }

impl Value {
    pub fn get_type(&self) -> ValueType {
        match self {
            Value::Logical(_) => ValueType::Logical,
            Value::Pointer(_) => ValueType::Pointer,
            Value::Character(_) => ValueType::Character,
            Value::Integer(_) => ValueType::Integer,
            Value::Float(_) => ValueType::Float,
            Value::Binary(_) => ValueType::Binary,
        }
    }
}

/// Holds the information needed to create an instance of `Expr`.
/// 
/// # Example
/// ```
/// # use csx64::asm::expr::*;
/// let ex: Expr = ExprData::Ident("foo".into()).into(); // points to the identifier "foo"
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
            ExprData::Value(Value::Pointer(value)) => {
                0xfdu8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Character(value)) => {
                0xfcu8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Integer(value)) => {
                0xfbu8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Float(value)) => {
                0xfau8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Value(Value::Binary(value)) => {
                0xf9u8.bin_write(f)?;
                value.bin_write(f)
            }
            ExprData::Ident(ident) => {
                0xf8u8.bin_write(f)?;
                ident.bin_write(f)
            }
            ExprData::Uneval { op, left, right } => {
                match right {
                    None => {
                        (*op as u8).bin_write(f)?;
                        left.as_ref().expect("left branch of expr cannot be empty").bin_write(f)
                    }
                    Some(right) => {
                        debug_assert!(*op as u8 <= 0x7f);
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
            0xfd => Ok(Value::Pointer(BinaryRead::bin_read(f)?).into()),
            0xfc => Ok(Value::Character(BinaryRead::bin_read(f)?).into()),
            0xfb => Ok(Value::Integer(BinaryRead::bin_read(f)?).into()),
            0xfa => Ok(Value::Float(BinaryRead::bin_read(f)?).into()),
            0xf9 => Ok(Value::Binary(BinaryRead::bin_read(f)?).into()),
            0xf8 => Ok(ExprData::Ident(String::bin_read(f)?)),
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
impl Debug for ExprData {
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
impl Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", &*self.data.borrow())
    }
}
/// Convenience for creating expressions from the raw type `ExprData`.
impl<T> From<T> for Expr where ExprData: From<T> {
    fn from(val: T) -> Self {
        Expr { data: RefCell::new(val.into()) }
    }
}

/// An appendonly map-like collection of defined symbols.
/// 
/// Importantly, an instance of this type is used during assembly/linking to facilitate pre- and user-defined symbols.
/// 
/// The type `T` is a tag type that is associated with the value to give it additional context.
/// For instance, the assembler uses tags to keep track of declaration line numbers.
/// 
/// # Example
/// ```
/// # use csx64::asm::expr::*;
/// let mut symbols: SymbolTable<usize> = Default::default();
/// symbols.define("foo".into(), 2u64.into(), 0).unwrap();
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
#[derive(Clone, Default)]
pub struct SymbolTable<T> {
    pub(super) raw: HashMap<String, (Expr, T)>,
}
impl<T> BinaryWrite for SymbolTable<T> where T: BinaryWrite {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.raw.bin_write(f)
    }
}
impl<T> BinaryRead for SymbolTable<T> where T: BinaryRead {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Self> {
        Ok(SymbolTable { raw: BinaryRead::bin_read(f)? })
    }
}
impl<T> Debug for SymbolTable<T> where T: Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (k, v) in self.iter() {
            writeln!(f, "{} := {:?}", k, v)?;
        }
        Ok(())
    }
}

/// The specific reason why an illegal operation failed.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum IllegalReason {
    IncompatibleTypes(OP, ValueType, ValueType),
    IncompatibleType(OP, ValueType),
    CyclicDependency,

    DivideByZero,
    PointerUnderflow,
    PointerOverflow,
    IntegerTooLarge,
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
impl From<IllegalReason> for EvalError {
    fn from(reason: IllegalReason) -> Self {
        EvalError::Illegal(reason)
    }
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
    assert!(all_legal(&[&Ok(Expr::from(34u64).value_ref()), &Ok(Expr::from(Float::with_val(FLOAT_PRECISION, 3.42)).value_ref())]).is_ok());
    assert!(all_legal(&[&Ok(Expr::from(54u64).value_ref()), &Err(EvalError::UndefinedSymbol("heloo".into()))]).is_ok());
    assert!(all_legal(&[&Err(EvalError::UndefinedSymbol("heloo".into())), &Err(EvalError::UndefinedSymbol("heloo".into()))]).is_ok());
    match all_legal(&[&Err(EvalError::Illegal(IllegalReason::IncompatibleType(OP::Not, ValueType::Float))), &Err(EvalError::UndefinedSymbol("heloo".into()))]) {
        Err(EvalError::Illegal(IllegalReason::IncompatibleType(OP::Not, ValueType::Float))) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Err(EvalError::UndefinedSymbol("heloo".into())), &Err(EvalError::Illegal(IllegalReason::IncompatibleTypes(OP::Add, ValueType::Integer, ValueType::Integer)))]) {
        Err(EvalError::Illegal(IllegalReason::IncompatibleTypes(OP::Add, ValueType::Integer, ValueType::Integer))) => (),
        _ => panic!("wrong"),
    }
    match all_legal(&[&Ok(Expr::from(463i64).value_ref()), &Err(EvalError::Illegal(IllegalReason::IncompatibleTypes(OP::Div, ValueType::Binary, ValueType::Logical)))]) {
        Err(EvalError::Illegal(IllegalReason::IncompatibleTypes(OP::Div, ValueType::Binary, ValueType::Logical))) => (),
        _ => panic!("wrong"),
    }
}

pub trait SymbolTableCore {
    /// Checks if the symbol table is empty.
    fn is_empty(&self) -> bool;
    /// Gets the number of defined symbols.
    fn len(&self) -> usize;
    /// Checks if a symbol with the given name has already been defined.
    fn is_defined(&self, symbol: &str) -> bool;
    /// Gets the associated expression if defined
    fn get_expr(&self, symbol: &str) -> Option<&Expr>;
}
impl<T> SymbolTableCore for SymbolTable<T> {
    fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }
    fn len(&self) -> usize {
        self.raw.len()
    }
    fn is_defined(&self, symbol: &str) -> bool {
        self.raw.contains_key(symbol)
    }
    fn get_expr(&self, symbol: &str) -> Option<&Expr> {
        self.get(symbol).map(|x| &x.0)
    }
}
impl<T> SymbolTable<T> {
    /// Constructs an empty symbol table.
    pub fn new() -> Self {
        Self { raw: Default::default() }
    }

    /// Introduces a new symbol.
    /// If not already defined, defines it and returns `Ok(())`.
    /// Otherwise, returns `Err(symbol)`.
    pub fn define(&mut self, symbol: String, value: Expr, tag: T) -> Result<(), String> {
        if !self.is_defined(&symbol) {
            self.raw.insert(symbol, (value, tag));
            Ok(())
        }
        else {
            Err(symbol)
        }
    }

    /// Gets the value of the given symbol if defined.
    pub fn get(&self, symbol: &str) -> Option<&(Expr, T)> {
        self.raw.get(symbol)
    }
    
    /// Undefines all symbols, effectively restoring the newly-constructed state.
    /// This is meant to support resource reuse, and should not be used to remove or modify defined symbols.
    pub fn clear(&mut self) {
        self.raw.clear();
    }
    
    /// Iterates over the defined symbols and their values.
    pub fn iter(&self) -> impl Iterator<Item = (&String, &(Expr, T))> + FusedIterator {
        self.raw.iter()
    }
}
#[test]
fn test_symbol_table() {
    let mut s: SymbolTable<()> = Default::default();
    assert!(!s.is_defined("foo"));
    assert!(!s.is_defined("bar"));
    s.define("foo".into(), ExprData::Ident("bar".into()).into(), ()).unwrap();
    assert!(s.is_defined("foo"));
    assert!(!s.is_defined("bar"));
    assert_eq!(s.define("foo".into(), ExprData::Ident("bar".into()).into(), ()).unwrap_err(), "foo");
}

pub(super) struct ValueRef<'a>(cell::Ref<'a, ExprData>);
impl<'a> Deref for ValueRef<'a> {
    type Target = Value;
    fn deref(&self) -> &Value {
        match &*self.0 {
            ExprData::Value(val) => val,
            _ => unreachable!(),
        }
    }
}
impl<'a> Debug for ValueRef<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", (*self).deref())
    }
}

pub(super) enum ValueCow<'a> {
    Owned(Value),
    Borrowed(ValueRef<'a>),
}
impl<'a> ValueCow<'a> {
    pub(super) fn into_owned(self) -> Value {
        match self {
            ValueCow::Owned(v) => v,
            ValueCow::Borrowed(v) => (*v).clone(),
        }
    }
}
impl<'a> Deref for ValueCow<'a> {
    type Target = Value;
    fn deref(&self) -> &Value {
        match self {
            ValueCow::Owned(v) => v,
            ValueCow::Borrowed(v) => &*v,
        }
    }
}
impl<'a> Debug for ValueCow<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", (*self).deref())
    }
}

impl Expr {
    /// Gets the value of an expression which is already known to be evaluated (not just evaluatable).
    /// Panics if this is not the case.
    fn eval_evaluated<'a>(&'a self, symbols: &'a dyn SymbolTableCore) -> ValueRef<'a> {
        let handle = self.data.borrow();
        match &*handle {
            ExprData::Value(_) => ValueRef(handle),
            ExprData::Ident(ident) => symbols.get_expr(ident).unwrap().eval_evaluated(symbols),
            ExprData::Uneval { .. } => panic!(),
        }
    }
    fn into_eval_evaluated<'a>(self, symbols: &'a dyn SymbolTableCore) -> ValueCow<'a> {
        match self.data.into_inner() {
            ExprData::Value(v) => ValueCow::Owned(v),
            ExprData::Ident(ident) => ValueCow::Borrowed(symbols.get_expr(&ident).unwrap().eval_evaluated(symbols)),
            ExprData::Uneval { .. } => panic!(),
        }
    }

    /// As `eval()` except that it consumes `self` and returns a `ValueCow`.
    /// This is similar to `std::borrow::Cow` (implements `Deref` and has an `into_owned()`).
    /// Currently, to appease the borrow checker this requires two separate evaluation passes (though they short circuit and the second should be very fast).
    /// Thus, if all you need is an (immutable) reference, you should stick with `eval()`.
    pub(super) fn into_eval<'a>(self, symbols: &'a dyn SymbolTableCore) -> Result<ValueCow<'a>, EvalError> {
        self.eval(symbols)?; // make sure we're evaluatable
        Ok(self.into_eval_evaluated(symbols))
    }
    /// Attempts to evaluate the expression given a symbol table to use.
    /// Due to reasons discussed in the doc entry for `SymbolTable`, once an `Expr` has been evaluated with a given symbol table
    /// it should never be evaluated with any other symbol table.
    pub(super) fn eval<'a>(&'a self, symbols: &'a dyn SymbolTableCore) -> Result<ValueRef<'a>, EvalError> {
        self.eval_recursive(symbols, &mut Default::default())
    }
    fn eval_recursive<'a>(&'a self, symbols: &'a dyn SymbolTableCore, visited: &mut HashSet<String>) -> Result<ValueRef<'a>, EvalError> {
        {
            let handle = match self.data.try_borrow() {
                Err(_) => return Err(IllegalReason::CyclicDependency.into()),
                Ok(h) => h,
            };
            match &*handle {
                ExprData::Value(_) => return Ok(ValueRef(handle)), // if we're a value node, we already have the value
                ExprData::Ident(ident) => match symbols.get_expr(ident) { // if it's an identifier, look it up
                    None => return Err(EvalError::UndefinedSymbol(ident.clone())),
                    Some(entry) => {
                        if !visited.insert(ident.clone()) { return Err(IllegalReason::CyclicDependency.into()); }
                        let res = entry.eval_recursive(symbols, visited);
                        visited.remove(ident);
                        return res;
                    }
                }
                ExprData::Uneval { .. } => (), // we do this next - totally different
            }
        }

        {
            let mut handle = self.data.borrow_mut();
            let res: Value = match &mut *handle {
                ExprData::Value(_) => unreachable!(), // these were already handled
                ExprData::Ident(_) => unreachable!(),
                ExprData::Uneval { op, ref mut left, right } => {
                    fn binary_op<'a, F, G>(raw_left: &'a mut Option<Box<Expr>>, raw_right: &'a Option<Box<Expr>>, symbols: &'a dyn SymbolTableCore, visited: &mut HashSet<String>, f: F, g: G) -> Result<Value, EvalError>
                    where F: FnOnce(&Value, &Value) -> Result<Option<Value>, EvalError>, G: FnOnce(Value, &Value) -> Value
                    {
                        {
                            let left = raw_left.as_ref().expect("expr binary op node missing left branch").eval_recursive(symbols, visited);
                            let right = raw_right.as_ref().expect("expr binary op node missing right branch").eval_recursive(symbols, visited);
                            all_legal(&[&left, &right])?; // if either was illegal, handle that first
                            if let Some(res) = f(&*left?, &*right?)? { return Ok(res); } // then handle other errors and the ref success case
                        }
                        Ok(g((*raw_left.take().unwrap()).into_eval_evaluated(symbols).into_owned(), &*raw_right.as_ref().unwrap().eval_evaluated(symbols)))
                    }
                    fn unary_op<'a, F, G>(raw_left: &'a mut Option<Box<Expr>>, raw_right: &'a Option<Box<Expr>>, symbols: &'a dyn SymbolTableCore, visited: &mut HashSet<String>, f: F, g: G) -> Result<Value, EvalError>
                    where F: FnOnce(&Value) -> Result<Option<Value>, EvalError>, G: FnOnce(Value) -> Value
                    {
                        if let Some(_) = raw_right.as_ref() { panic!("expr unary op node had a right branch"); }
                        let left = raw_left.as_ref().expect("expr unary op node was missing the left branch").eval_recursive(symbols, visited);
                        if let Some(res) = f(&*left?)? { return Ok(res); }
                        Ok(g((*raw_left.take().unwrap()).into_eval_evaluated(symbols).into_owned()))
                    }

                    match op {
                        OP::Mul => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Integer(_), Value::Integer(_)) => Ok(None),
                                (Value::Float(_), Value::Float(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a * b).into(),
                                (Value::Float(a), Value::Float(b)) => (a * b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Div => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Integer(_), Value::Integer(b)) => if b.cmp0() != Ordering::Equal { Ok(None) } else { Err(IllegalReason::DivideByZero.into()) },
                                (Value::Float(_), Value::Float(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a / b).into(),
                                (Value::Float(a), Value::Float(b)) => (a / b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Mod => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Integer(_), Value::Integer(b)) => if b.cmp0() != Ordering::Equal { Ok(None) } else { Err(IllegalReason::DivideByZero.into()) },
                                (Value::Float(_), Value::Float(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a % b).into(),
                                (Value::Float(a), Value::Float(b)) => (a % b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Add => {
                            fn handle_pointer_add(ptr: u64, int: &Integer) -> Result<Option<Value>, EvalError> {
                                let res = Integer::from(ptr) + int;
                                match res.to_u64() {
                                    None => Err(if res.cmp0() == Ordering::Less { IllegalReason::PointerUnderflow } else { IllegalReason::PointerOverflow }.into()),
                                    Some(v) => Ok(Some(Value::Pointer(v))),
                                }
                            }

                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Pointer(a), Value::Integer(b)) => handle_pointer_add(*a, b),
                                (Value::Integer(a), Value::Pointer(b)) => handle_pointer_add(*b, a),
                                (Value::Integer(_), Value::Integer(_)) => Ok(None),
                                (Value::Float(_), Value::Float(_)) => Ok(None),
                                (Value::Binary(_), Value::Binary(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a + b).into(),
                                (Value::Float(a), Value::Float(b)) => (a + b).into(),
                                (Value::Binary(mut a), Value::Binary(b)) => { a.extend_from_slice(b); a.into() }
                                _ => unreachable!(),
                            })?
                        },
                        OP::Sub => {
                            fn handle_pointer_sub(ptr: u64, int: &Integer) -> Result<Option<Value>, EvalError> {
                                let res = Integer::from(ptr) - int;
                                match res.to_u64() {
                                    None => Err(if res.cmp0() == Ordering::Less { IllegalReason::PointerOverflow } else { IllegalReason::PointerUnderflow }.into()),
                                    Some(v) => Ok(Some(Value::Pointer(v))),
                                }
                            }

                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Pointer(a), Value::Integer(b)) => handle_pointer_sub(*a, b),
                                (Value::Integer(_), Value::Integer(_)) => Ok(None),
                                (Value::Float(_), Value::Float(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a - b).into(),
                                (Value::Float(a), Value::Float(b)) => (a - b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::SHL => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => {
                                    if a.cmp0() == Ordering::Equal { return Ok(Some(0.into())); }
                                    let shift = match b.to_i32() {
                                        None => return Err(IllegalReason::IntegerTooLarge.into()),
                                        Some(v) => v,   
                                    };
                                    if a.significant_bits() as i32 + shift > INT_PRECISION as i32 { return Err(IllegalReason::IntegerTooLarge.into()); }
                                    Ok(None)
                                },
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a << b.to_i32().unwrap()).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::SHR => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => {
                                    if a.cmp0() == Ordering::Equal { return Ok(Some(0.into())); }
                                    let shift = match b.to_i32() {
                                        None => return Err(IllegalReason::IntegerTooLarge.into()),
                                        Some(v) => v,   
                                    };
                                    if a.significant_bits() as i32 + shift > INT_PRECISION as i32 { return Err(IllegalReason::IntegerTooLarge.into()); }
                                    Ok(None)
                                },
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a >> b.to_i32().unwrap()).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Less => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Pointer(a), Value::Pointer(b)) => Ok(Some((a < b).into())),
                                (Value::Integer(a), Value::Integer(b)) => Ok(Some((a < b).into())),
                                (Value::Float(a), Value::Float(b)) => Ok(Some((a < b).into())),
                                (Value::Binary(a), Value::Binary(b)) => Ok(Some((a < b).into())),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |_, _| unreachable!())?
                        },
                        OP::LessE => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Pointer(a), Value::Pointer(b)) => Ok(Some((a <= b).into())),
                                (Value::Integer(a), Value::Integer(b)) => Ok(Some((a <= b).into())),
                                (Value::Float(a), Value::Float(b)) => Ok(Some((a <= b).into())),
                                (Value::Binary(a), Value::Binary(b)) => Ok(Some((a <= b).into())),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |_, _| unreachable!())?
                        },
                        OP::Great => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Pointer(a), Value::Pointer(b)) => Ok(Some((a > b).into())),
                                (Value::Integer(a), Value::Integer(b)) => Ok(Some((a > b).into())),
                                (Value::Float(a), Value::Float(b)) => Ok(Some((a > b).into())),
                                (Value::Binary(a), Value::Binary(b)) => Ok(Some((a > b).into())),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |_, _| unreachable!())?
                        },
                        OP::GreatE => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Pointer(a), Value::Pointer(b)) => Ok(Some((a >= b).into())),
                                (Value::Integer(a), Value::Integer(b)) => Ok(Some((a >= b).into())),
                                (Value::Float(a), Value::Float(b)) => Ok(Some((a >= b).into())),
                                (Value::Binary(a), Value::Binary(b)) => Ok(Some((a >= b).into())),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |_, _| unreachable!())?
                        },
                        OP::Equ => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Logical(a), Value::Logical(b)) => Ok(Some((a == b).into())),
                                (Value::Pointer(a), Value::Pointer(b)) => Ok(Some((a == b).into())),
                                (Value::Integer(a), Value::Integer(b)) => Ok(Some((a == b).into())),
                                (Value::Float(a), Value::Float(b)) => Ok(Some((a == b).into())),
                                (Value::Binary(a), Value::Binary(b)) => Ok(Some((a == b).into())),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |_, _| unreachable!())?
                        },
                        OP::Neq => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Logical(a), Value::Logical(b)) => Ok(Some((a != b).into())),
                                (Value::Pointer(a), Value::Pointer(b)) => Ok(Some((a != b).into())),
                                (Value::Integer(a), Value::Integer(b)) => Ok(Some((a != b).into())),
                                (Value::Float(a), Value::Float(b)) => Ok(Some((a != b).into())),
                                (Value::Binary(a), Value::Binary(b)) => Ok(Some((a != b).into())),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |_, _| unreachable!())?
                        },
                        OP::And => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Logical(a), Value::Logical(b)) => Ok(Some((*a && *b).into())),
                                (Value::Integer(_), Value::Integer(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a & b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Or => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Logical(a), Value::Logical(b)) => Ok(Some((*a || *b).into())),
                                (Value::Integer(_), Value::Integer(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a | b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Xor => {
                            binary_op(left, &right, symbols, visited, |a, b| match (a, b) {
                                (Value::Logical(a), Value::Logical(b)) => Ok(Some((*a ^ *b).into())),
                                (Value::Integer(_), Value::Integer(_)) => Ok(None),
                                (a, b) => Err(IllegalReason::IncompatibleTypes(*op, a.get_type(), b.get_type()).into()),
                            }, |a, b| match (a, b) {
                                (Value::Integer(a), Value::Integer(b)) => (a ^ b).into(),
                                _ => unreachable!(),
                            })?
                        },
                        OP::Neg => {
                            unary_op(left, &right, symbols, visited, |a| match a {
                                Value::Integer(_) => Ok(None),
                                Value::Float(_) => Ok(None),
                                a => Err(IllegalReason::IncompatibleType(*op, a.get_type()).into()),
                            }, |a| match a {
                                Value::Integer(a) => (-a).into(),
                                Value::Float(a) => (-a).into(),
                                _ => unreachable!(),
                            })?
                        }
                        OP::Not => {
                            unary_op(left, &right, symbols, visited, |a| match a {
                                Value::Logical(a) => Ok(Some((!a).into())),
                                Value::Integer(_) => Ok(None),
                                a => Err(IllegalReason::IncompatibleType(*op, a.get_type()).into()),
                            }, |a| match a {
                                Value::Integer(a) => (!a).into(),
                                _ => unreachable!(),
                            })?
                        }
                        OP::Condition => {
                            let (cond, pair) = match (left.as_ref(), right.as_ref()) {
                                (Some(a), Some(b)) => (a.eval(symbols), b),
                                _ => panic!(),
                            };
                            match &mut *pair.data.borrow_mut() {
                                ExprData::Uneval { op: OP::Pair, left, right } => {
                                    let cond = {
                                        let (r1, r2) = match (left.as_ref(), right.as_ref()) {
                                            (Some(a), Some(b)) => (a.eval(symbols), b.eval(symbols)),
                                            _ => panic!(),
                                        };
                                        all_legal(&[&cond, &r1, &r2])?; // if any were illegal, handle that first
                                        let (cond, _, _) = (cond?, r1?, r2?); // then handle other errors

                                        match &*cond {
                                            Value::Logical(v) => *v,
                                            a => return Err(IllegalReason::IncompatibleType(OP::Condition, a.get_type()).into()),
                                        }
                                    };
                                    let res = if cond { left.take() } else { right.take() };
                                    res.unwrap().into_eval_evaluated(symbols).into_owned()
                                }
                                _ => panic!(), // ill formed
                            }
                        }
                        OP::Pair => panic!(), // ill formed
                    }
                }
            };

            // we successfully evaluated it - collapse to just a value node
            *handle = ExprData::Value(res);
        }

        Ok(ValueRef(self.data.borrow()))
    }

    /// Breaks an expression up into a set of positive terms and negative terms.
    /// Assuming +/- are associative, + is commutative, and - is anticommutative,
    /// the expr is reconstructed as sum(res.0)-sum(res.1).
    pub(super) fn break_add_sub(self) -> (Vec<Expr>, Vec<Expr>) {
        let mut add = vec![];
        let mut sub = vec![];
        self.recursive_break_add_sub(&mut add, &mut sub); // refer to the recursive helper starting with empty lists
        (add, sub)
    }
    fn recursive_break_add_sub(self, add: &mut Vec<Expr>, sub: &mut Vec<Expr>) {
        match self.data.into_inner() {
            ExprData::Uneval { op: OP::Add, left, right } => {
                left.unwrap().recursive_break_add_sub(add, sub);
                right.unwrap().recursive_break_add_sub(add, sub);
            }
            ExprData::Uneval { op: OP::Sub, left, right } => {
                left.unwrap().recursive_break_add_sub(add, sub);
                right.unwrap().recursive_break_add_sub(sub, add);
            }
            ExprData::Uneval { op: OP::Neg, left, right: _ } => {
                left.unwrap().recursive_break_add_sub(sub, add);
            }
            x => add.push(x.into()),
        }
    }

    // chains the exprs together by addition (left associative).
    pub(super) fn chain_add(add: Vec<Expr>) -> Option<Expr> {
        let mut add = add.into_iter().fuse();
        let mut res = add.next();
        for expr in add {
            let sum = (OP::Add, res.take().unwrap(), expr).into();
            res = Some(sum);
        }
        res
    }
    // chains the exprs together with addition subtraction (left associative)
    pub(super) fn chain_add_sub(add: Vec<Expr>, sub: Vec<Expr>) -> Option<Expr> {
        match (add.is_empty(), sub.is_empty()) {
            (_, true) => Self::chain_add(add),
            (true, false) => Some((OP::Neg, Self::chain_add(sub).unwrap()).into()),
            (false, false) => Some((OP::Sub, Self::chain_add(add).unwrap(), Self::chain_add(sub).unwrap()).into()),
        }
    }

    #[cfg(test)]
    fn value_ref(&self) -> ValueRef {
        let handle = self.data.borrow();
        match &*handle {
            ExprData::Value(_) => ValueRef(handle),
            _ => panic!(),
        }
    }
}
#[test]
fn test_catch_cyclic_dep() {
    let mut s: SymbolTable<()> = Default::default();

    s.define("foo".into(), ExprData::Ident("bar".into()).into(), ()).unwrap();
    s.define("bar".into(), ExprData::Ident("foo".into()).into(), ()).unwrap();

    match s.get("foo").unwrap().0.eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }
    match s.get("bar").unwrap().0.eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }

    s.define("solipsis".into(), ExprData::Ident("solipsis".into()).into(), ()).unwrap();

    match s.get("solipsis").unwrap().0.eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }

    s.define("piano".into(), (OP::Add, ExprData::Ident("piano".into()), Expr::from(1i64)).into(), ()).unwrap();

    match s.get("piano").unwrap().0.eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }
    match Expr::from(ExprData::Ident("piano".into())).eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }

    s.define("a".into(), (OP::Add, ExprData::Ident("b".into()), ExprData::Ident("b".into())).into(), ()).unwrap();
    s.define("b".into(), (OP::Add, ExprData::Ident("a".into()), ExprData::Ident("a".into())).into(), ()).unwrap();

    match s.get("a").unwrap().0.eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }
    match Expr::from(ExprData::Ident("a".into())).eval(&s) {
        Err(EvalError::Illegal(IllegalReason::CyclicDependency)) => (),
        x => panic!("{:?}", x),
    }

    ()
}

#[test]
fn test_expr_eval() {
    let mut s: SymbolTable<()> = Default::default();
    macro_rules! make_expr {
        ($op:expr, $left:expr, $right:expr) => {
            Expr::from(($op, ExprData::from($left), ExprData::from($right)))
        }
    }

    // this is not exhaustive by any means.
    // more thorough testing will be done indirectly by testing the assembler.


    match make_expr!(OP::Mul, 4, 6).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 24),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mul, -4, 6).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, -24),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mul, 4, -6).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, -24),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mul, -4, -6).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 24),
        v => panic!("{:?}", v),
    }

    // --------------------------------------------------------------------------------

    match make_expr!(OP::Div, 57, 10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 5),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Div, -57, 10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, -5),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Div, 57, -10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, -5),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Div, -57, -10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 5),
        v => panic!("{:?}", v),
    }

    // --------------------------------------------------------------------------------

    match make_expr!(OP::Mod, 57, 10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 7),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mod, -57, 10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, -7),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mod, 57, -10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 7),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mod, -57, -10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, -7),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Mod, -57, 0).into_eval(&s) {
        Err(e) => match e {
            EvalError::Illegal(IllegalReason::DivideByZero) => (),
            _ => panic!("{:?}", e),
        }
        Ok(v) => panic!("{:?}", v),
    }

    // --------------------------------------------------------------------------------


    // make sure that the new take() logic is safe when used on Ident (make sure it takes a copy, not the actual symbol value)
    s.define("foo".into(), 654.into(), ()).unwrap();
    match Expr::from(ExprData::Ident("foo".into())).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 654),
        v => panic!("{:?}", v),
    }
    match Expr::from(ExprData::Ident("foo".into())).into_eval(&s).unwrap().into_owned() { // do it twice - second time is the potential failure
        Value::Integer(v) => assert_eq!(v, 654),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Add, ExprData::Ident("foo".into()), 10).into_eval(&s).unwrap().into_owned() {
        Value::Integer(v) => assert_eq!(v, 664),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Add, ExprData::Ident("foo".into()), 10).into_eval(&s).unwrap().into_owned() { // do it twice - second time is the potential failure
        Value::Integer(v) => assert_eq!(v, 664),
        v => panic!("{:?}", v),
    }

    s.define("msg".into(), "owo wats dis".as_bytes().to_owned().into(), ()).unwrap();
    s.define("msg2".into(), "rawr xd".as_bytes().to_owned().into(), ()).unwrap();

    match Expr::from(ExprData::Ident("msg".into())).into_eval(&s).unwrap().into_owned() {
        Value::Binary(v) => assert_eq!(v, "owo wats dis".as_bytes()),
        v => panic!("{:?}", v),
    }
    match Expr::from(ExprData::Ident("msg".into())).into_eval(&s).unwrap().into_owned() { // do it twice - second time is the potential failure
        Value::Binary(v) => assert_eq!(v, "owo wats dis".as_bytes()),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Add, ExprData::Ident("msg".into()), ExprData::Ident("msg2".into())).into_eval(&s).unwrap().into_owned() {
        Value::Binary(v) => assert_eq!(v, "owo wats disrawr xd".as_bytes()),
        v => panic!("{:?}", v),
    }
    match make_expr!(OP::Add, ExprData::Ident("msg".into()), ExprData::Ident("msg2".into())).into_eval(&s).unwrap().into_owned() { // do it twice - second time is the potential failure
        Value::Binary(v) => assert_eq!(v, "owo wats disrawr xd".as_bytes()),
        v => panic!("{:?}", v),
    }
}
