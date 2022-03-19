use std::ops::Range;
use rug::{Integer as RugInt, Float as RugFloat};

pub const CTIME_FLOAT_BITS: u32 = 128;

lalrpop_mod!(#[allow(all, clippy::all)] pub grammar, "/crust/grammar.rs"); // clippy goes crazy on the generated code

macro_rules! raw_span_impl {
    ($($t:ty),+$(,)?) => {$(
        impl Spanned for $t { fn span(&self) -> Span { self.raw_span } }
    )*}
}

// ---------------------------------------------------------------------

#[derive(Debug)]
pub enum AstError {
    CStyleOctal { span: Span },
}

#[derive(Clone, Copy, Debug)]
pub struct Span(usize, usize);
impl Span {
    pub fn to_range(&self) -> Range<usize> { self.0..self.1 }
}
pub trait Spanned {
    fn span(&self) -> Span;
}

// ---------------------------------------------------------------------

#[derive(Debug)]
pub enum Item<'a> {
    Function(Function<'a>),
}

#[derive(Debug)]
pub struct Function<'a> {
    pub ret: Type<'a>,
    pub name: Ident<'a>,
    pub params: Vec<Param<'a>>,
    pub body: Vec<Stmt<'a>>,
}
#[derive(Debug)]
pub struct Param<'a> {
    pub name: Ident<'a>,
    pub ty: Type<'a>,
}

// ---------------------------------------------------------------------

#[derive(Debug)]
pub enum Stmt<'a> {
    VarDecl { ty: Type<'a>, name: Ident<'a>, value: Expr },
}

#[derive(Debug)]
pub enum Expr {
    Value(Value),
}

#[derive(Debug)]
pub enum Value {
    Integer(Integer),
    Float(Float),
}

// ---------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
pub enum IntType {
    U8, U16, U32, U64, U128, Usize,
    I8, I16, I32, I64, I128, Isize,
}
#[derive(Clone, Copy, Debug)]
pub enum FloatType { F32, F64, F80 }

#[derive(Debug)]
pub enum Type<'a> {
    Void,
    Integer(IntType),
    Float(FloatType),
    Pointer { target: Box<Type<'a>>, is_const: bool },
    UserDefined { name: Ident<'a> },
}

// ---------------------------------------------------------------------

#[derive(Debug)] pub struct Ident<'a> { pub id: &'a str, pub raw_span: Span }
#[derive(Debug)] pub struct Bool { pub value: bool, pub raw_span: Span }
#[derive(Debug)] pub struct Integer { pub value: RugInt, pub ty: Option<IntType>, pub raw_span: Span }
#[derive(Debug)] pub struct Float { pub value: RugFloat, pub ty: Option<FloatType>, pub raw_span: Span }

raw_span_impl! { Ident<'_>, Bool, Integer, Float }