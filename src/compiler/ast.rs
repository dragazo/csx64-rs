use std::ops::Range;
use rug::Integer as RugInt;

lalrpop_mod!(#[allow(all, clippy::all)] grammar, "/compiler/grammar.rs"); // clippy goes crazy on the generated code

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

#[derive(Clone, Debug)]
pub struct Ident<'a> { name: &'a str, raw_span: Span }
impl Spanned for Ident<'_> { fn span(&self) -> Span { self.raw_span } }

#[derive(Clone, Copy, Debug)]
enum IntType {
    U8, U16, U32, U64, U128, Usize,
    I8, I16, I32, I64, I128, Isize,
    Unknown,
}
pub struct Integer { value: RugInt, ty: IntType, raw_span: Span }
