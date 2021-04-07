//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, VecDeque};
use std::io::{self, Read, Write, BufRead};
use std::{mem, iter};
use std::cmp::Ordering;
use std::borrow::Cow;
use num_traits::FromPrimitive;

pub mod binary_set;
pub mod expr;
pub mod caseless;
mod constants;
mod asm_args;

use binary_set::BinarySet;
use expr::*;
use constants::*;
use asm_args::*;
use caseless::Caseless;

use crate::common::serialization::*;
use crate::common::f80::F80;
use crate::common::{OPCode, Executable, Syscall};

/// The types of errors associated with failed address parsing,
/// but for which we know the argument was intended to be an address.
#[derive(Debug)]
pub enum BadAddress {
    Unterminated,
    SizeMissingPtr,
    RegMultNotCriticalExpr(EvalError),
    /// A register was connected by an operation other than addition/subtraction.
    RegIllegalOp,
    /// Denotes invalid usage of register multipliers in an address expression.
    /// This is issued when the registers cannot be expressed as `a*r1 + r2` where `a` is 1, 2, 4, or 8.
    InvalidRegMults,
    ConflictingSizes,
    SizeUnsupported,
    TypeUnsupported,
    InteriorNotSingleExpr,
    PtrSpecWithoutSize,
    SizeNotRecognized,
    IllegalExpr(IllegalReason),
    BadBase,
}

/// The kinds of errors that can occur during assembly.
/// These are meant to be specific enough to have customized, detailed error messages.
#[derive(Debug)]
pub enum AsmErrorKind {
    /// A read error occurred, which cause assembly to halt prematurely.
    ReadError(io::Error),

    // --------------------------------------------------------------------------

    /// Incorrect number of arguments supplied. Expected this many.
    ArgsExpectedCount(&'static [u8]),
    /// Incorrect number of arguments supplied. Expected at least this many.
    ArgsExpectedCountAtLeast(u8),
    /// There was unknown content after the arguments list.
    ExtraContentAfterArgs,

    // --------------------------------------------------------------------------

    /// Failed to evaluate a critical expression for the given reason.
    FailedCriticalExpression(EvalError),

    /// The prefix on this instruction is not allowed.
    InvalidPrefixForThisInstruction,

    PrefixWithoutInstruction,
    
    ExpectedSegment,
    SegmentAlreadyCompleted,
    LabelOnSegmentLine,

    AssertFailure,
    AssertArgHadSizeSpec,
    AssertArgNotLogical(ValueType),

    ExpectedString,
    UnexpectedString,
    IncompleteString,
    IncompleteEscape,
    InvalidEscape,

    ExpectedExprTerm,
    ExpectedOpenParen,
    MissingCloseParen,
    UnexpectedOpenParen,
    UnexpectedCloseParen,
    ParenInteriorNotExpr,
    ExpectedCommaBeforeToken,
    UnrecognizedMacroInvocation,

    UseOfTildeNot,

    IllFormedNumericLiteral,
    NumericLiteralWithZeroPrefix,
    
    LocalSymbolBeforeNonlocal,
    InvalidSymbolName,
    ReservedSymbolName,

    ExpectedBinaryValue,
    EmptyBinaryValue,

    CharacterLiteralNotUnicode,
    CharacterLiteralNotSingleChar,

    LabelOutsideOfSegment,
    SymbolAlreadyDefined,
    IllegalInCurrentSegment,
    TimesIterOutisideOfTimes,

    ExpectedAddress,
    BadAddress(BadAddress),
    
    TimesMissingCount,
    TimesCountNotImm,
    TimesCountHadSizeSpec,
    TimesCountNotCriticalExpression,
    TimesCountNotInteger,
    TimesCountWasNegative,
    TimesCountTooLarge,
    TimesUsedOnEmptyLine,

    IfMissingExpr,
    IfExprNotImm,
    IfExprHadSizeSpec,
    IfExprNotCriticalExpression,
    IfExprNotLogical,
    IfUsedOnEmptyLine,

    UnrecognizedInstruction,

    ExpectedExpressionArg(u8),

    WriteOutsideOfSegment,
    WriteInBssSegment,
    InstructionOutsideOfTextSegment,

    IllegalPatch(IllegalPatchReason),

    ExprIllegalError(IllegalReason),

    UnsupportedOperandSize,
    OperandsHadDifferentSizes,
    ForcedSizeViolation,
    CouldNotDeduceOperandSize,
    
    TernaryOpUnsupportedTypes,
    BinaryOpUnsupportedTypes,
    UnaryOpUnsupportedType,
    ValueOpUnsupportedType,
    BinaryLvalueOpUnsupportedTypes,
    BinaryLvalueUnorderedOpUnsupportedTypes,
    FPUBinaryOpUnsupportedTypes,

    FPUBinaryOpNeitherST0,
    FPUBinaryOpPop2SrcNotST0,

    EQUWithoutLabel,
    EQUArgumentHadSizeSpec,

    AlignArgumentHadSizeSpec,
    AlignValueNotExpr,
    AlignValueNotCriticalExpr,
    AlignValueNotPowerOf2,
    AlignValueNotInteger,
    AlignValueNegative,
    AlignValueExceedsMaxAlign,
    AlignOutsideOfSegment,

    DeclareValueHadSizeSpec,
    DeclareValueNotExpr,

    ReserveValueNotExpr,
    ReserveValueHadSizeSpec,
    ReserveValueNotCriticalExpr,
    ReserveValueNegative,
    ReserveValueNotInteger,
    ReserveValueTooLarge,
    ReserveOutsideOfBss,

    ExpectedIdentifier,
    IdentifierHadSizeSpec,
    IdentifierIsGlobalAndExtern,
    RedundantGlobalOrExternDecl { prev_line_num: usize },

    LEADestNotRegister,
    LEADestByte,
    LEASrcNotAddress,

    GlobalSymbolWasNotDefined,
    UnknownSymbol(String),

    StringDeclareNotByteSize,

    VPUMaskNotRecognized,
    VPUMaskUnclosedBracket,
    VPUZeroingWithoutOpmask,
    VPUOpmaskWasK0,
    VPUMaskUnrecognizedMode,
}
impl From<BadAddress> for AsmErrorKind {
    fn from(reason: BadAddress) -> Self {
        AsmErrorKind::BadAddress(reason)
    }
}

#[derive(Debug)]
pub struct AsmError {
    /// The type of error that was encountered.
    pub kind: AsmErrorKind,
    /// Line number of the error.
    pub line_num: usize,
    /// Byte index of the error in the line (if relevant).
    pub pos: Option<usize>,
    /// Error which caused this error (if relevant).
    pub inner_err: Option<Box<AsmError>>,
}

#[derive(Debug)]
pub enum LinkError {
    NothingToLink,

    EntryPointSourceNotExtern,
    EntryPointTargetNotValidIdent,
    EntryPointTargetWasReservedSymbol,
    EntryPointTargetAlreadyExisted,
    EntryPointTargetNotDefined,

    GlobalSymbolMultipleSources { ident: String, src1: (String, usize), src2: (String, usize) },
    ExternSymbolNotDefined { ident: String, required_by: String },
    
    EvalFailure { src: String, line_num: usize, reason: EvalError },
    PatchIllegal { src: String, line_num: usize, reason: IllegalPatchReason },
}

/// Grabs the first alphanumeic substring (skipping leading white space).
/// Returns the found token (or empty string if none) and the index just after it.
fn grab_alnum_token(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    let token_start = match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        None => raw_stop,
        Some(p) => raw_start + p,
    };
    let token_stop = match raw_line[token_start..raw_stop].find(|c: char| !c.is_ascii_alphanumeric()) {
        None => raw_stop,
        Some(p) => token_start + p,
    };
    (&raw_line[token_start..token_stop], token_stop)
}
#[test]
fn test_grab_alnum_token() {
    assert_eq!(grab_alnum_token("   \t hel$lo world  ", 3, 18), ("hel", 8));
    assert_eq!(grab_alnum_token("    \t  ", 1, 7), ("", 7));
    assert_eq!(grab_alnum_token("", 0, 0), ("", 0));
    assert_eq!(grab_alnum_token("  test,;comment  ", 1, 17), ("test", 6));
    assert_eq!(grab_alnum_token("  test; comment  ", 1, 17), ("test", 6));
    assert_eq!(grab_alnum_token("  ;test; comment  ", 1, 17), ("", 2));
}

/// Grabs the first whitespace-separated token and returns it, along with the index just after it.
/// If no token is present, returns empty string and the index of one past the end of the input string.
/// This function is comment-aware and will treat a comment character as a stopping point.
fn grab_whitespace_sep_token(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    let token_start = match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        None => raw_stop,
        Some(p) => raw_start + p,
    };
    let token_stop = match raw_line[token_start..raw_stop].find(|c: char| c.is_whitespace() || c == COMMENT_CHAR) {
        None => raw_stop,
        Some(p) => token_start + p,
    };
    (&raw_line[token_start..token_stop], token_stop)
}
#[test]
fn test_grab_ws_sep_token() {
    assert_eq!(grab_whitespace_sep_token("   \t hello world  ", 3, 18), ("hello", 10));
    assert_eq!(grab_whitespace_sep_token("    \t  ", 1, 7), ("", 7));
    assert_eq!(grab_whitespace_sep_token("", 0, 0), ("", 0));
    assert_eq!(grab_whitespace_sep_token("  test;comment  ", 1, 16), ("test", 6));
    assert_eq!(grab_whitespace_sep_token("  test; comment  ", 1, 17), ("test", 6));
    assert_eq!(grab_whitespace_sep_token("  ;test; comment  ", 1, 17), ("", 2));
}

/// Trims all leading whitespace characters and returns the result and the index of the starting portion.
/// If the string is empty or whitespace, returns empty string and one past the end of the input string.
fn trim_start_with_pos(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        Some(p) => {
            let mut r = (&raw_line[raw_start + p..raw_stop], raw_start + p);
            if r.0.chars().next() == Some(COMMENT_CHAR) { r.0 = ""; } // if we're on a comment char return empty string (but same pos)
            r
        }
        None => ("", raw_stop),
    }
}
#[test]
fn test_trim_start_with_pos() {
    assert_eq!(trim_start_with_pos("   \t hello world  ", 3, 18), ("hello world  ", 5));
    assert_eq!(trim_start_with_pos("    \t  ", 1, 7), ("", 7));
    assert_eq!(trim_start_with_pos("", 0, 0), ("", 0));
    assert_eq!(trim_start_with_pos("   ;hello wrold", 1, 15), ("", 3));
}

fn is_valid_symbol_name(name: &str) -> bool {
    let mut chars = name.chars();
    match chars.next() {
        None => return false, // empty symbol name not allowed
        Some(c) => match c {
            '_' | 'a'..='z' | 'A'..='Z' => (), // first char
            _ => return false,
        }
    }
    for c in chars {
        match c {
            '_' | '.' | 'a'..='z' | 'A'..='Z' | '0'..='9' => (), // other chars
            _ => return false,
        }
    }
    true
}
#[test]
fn test_valid_symname() {
    assert!(is_valid_symbol_name("foo"));
    assert!(is_valid_symbol_name("Foo"));
    assert!(!is_valid_symbol_name(".foo"));
    assert!(is_valid_symbol_name("_foo"));
    assert!(!is_valid_symbol_name("._foo"));
    assert!(!is_valid_symbol_name(".7_foo"));
    assert!(!is_valid_symbol_name("12"));
    assert!(!is_valid_symbol_name("12.4"));
    assert!(!is_valid_symbol_name("7up"));
    assert!(is_valid_symbol_name("_7up"));
    assert!(!is_valid_symbol_name(" _7up"));
    assert!(!is_valid_symbol_name("_7up "));
    assert!(!is_valid_symbol_name("_7u p"));
    assert!(!is_valid_symbol_name("$foo"));
}

fn is_reserved_symbol_name(name: &str) -> bool {
    RESERVED_SYMBOLS.contains(&Caseless(name))
}
#[test]
fn test_reserved_symname() {
    assert!(!is_reserved_symbol_name("foo"));
    assert!(is_reserved_symbol_name("rax"));
    assert!(is_reserved_symbol_name("RaX"));
    assert!(is_reserved_symbol_name("truE"));
    assert!(is_reserved_symbol_name("False"));
    assert!(is_reserved_symbol_name("nUll"));
    assert!(is_reserved_symbol_name("pTr"));
    assert!(!is_reserved_symbol_name("main"));
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AsmSegment {
    Text = 1,
    Rodata = 2,
    Data = 4,
    Bss = 8,
}

#[derive(Clone, Debug)]
struct Imm {
    expr: Expr,
    size: Option<Size>, // size of the value
}

#[derive(Clone, Debug)]
struct Address {
    address_size: Size,         // size of the address itself
    r1: Option<(u8, u8)>,       // r1 and r1 mult
    r2: Option<u8>,             // r2 (mult of 1)
    base: Option<Expr>,         // constant base address - 0 if absent, but saves space in the binary
    pointed_size: Option<Size>, // size of the pointed-to value (not the address itself)
}

#[derive(Clone, Debug)]
enum VPUMaskType {
    Blend(VPUMaskRegisterInfo),
    Zero(VPUMaskRegisterInfo),
}

#[derive(Clone, Debug)]
enum Argument {
    CPURegister(CPURegisterInfo),
    FPURegister(FPURegisterInfo),
    VPURegister { reg: VPURegisterInfo, mask: Option<VPUMaskType> },
    Address(Address),
    Imm(Imm),
    Segment(AsmSegment),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Size {
    Byte,
    Word,
    Dword,
    Qword,

    Xword,
    Yword,
    Zword,

    Tword,
}
impl Size {
    /// Returns the size of this type in bytes.
    fn size(self) -> usize {
        match self {
            Size::Byte => 1,
            Size::Word => 2,
            Size::Dword => 4,
            Size::Qword => 8,
            Size::Xword => 16,
            Size::Yword => 32,
            Size::Zword => 64,
            Size::Tword => 10,
        }
    }

    /// If self is a basic size (byte, word, dword, qword), returns the sizecode (0, 1, 2, 3).
    fn basic_sizecode(self) -> Option<u8> {
        match self {
            Size::Byte => Some(0),
            Size::Word => Some(1),
            Size::Dword => Some(2),
            Size::Qword => Some(3),
            _ => None
        }
    }
    /// If self is a vector size (xword, yword, zword), returns the sizecode (0, 1, 2)
    fn vector_sizecode(self) -> Option<u8> {
        match self {
            Size::Xword => Some(0),
            Size::Yword => Some(1),
            Size::Zword => Some(2),
            _ => None
        }
    }
}
impl BinaryWrite for Size {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            Size::Byte => 0u8,
            Size::Word => 1,
            Size::Dword => 2,
            Size::Qword => 3,
            Size::Xword => 4,
            Size::Yword => 5,
            Size::Zword => 6,
            Size::Tword => 7,
        }.bin_write(f)
    }
}
impl BinaryRead for Size {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Size> {
        Ok(match u8::bin_read(f)? {
            0 => Size::Byte,
            1 => Size::Word,
            2 => Size::Dword,
            3 => Size::Qword,
            4 => Size::Xword,
            5 => Size::Yword,
            6 => Size::Zword,
            7 => Size::Tword,
            _ => return Err(io::ErrorKind::InvalidData.into()),
        })
    }
}
#[test]
fn test_size_fns() {
    assert_eq!(Size::Byte.basic_sizecode(), Some(0));
    assert_eq!(Size::Dword.vector_sizecode(), None);
    assert_eq!(Size::Dword.size(), 4);
    assert_eq!(Size::Xword.basic_sizecode(), None);
    assert_eq!(Size::Xword.vector_sizecode(), Some(0));
    assert_eq!(Size::Xword.size(), 16);
    assert_eq!(Size::Yword.vector_sizecode(), Some(1));
    assert_eq!(Size::Yword.size(), 32);
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, FromPrimitive)]
#[repr(u8)]
pub enum HoleType {
    Pointer, // only pointer
    Integer, // integer or pointer
    Float,   // only float
    Any,     // anything (used for e.g. dd)
}
impl BinaryWrite for HoleType {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        (*self as u8).bin_write(f)
    }
}
impl BinaryRead for HoleType {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<HoleType> {
        match HoleType::from_u8(u8::bin_read(f)?) {
            None => return Err(io::ErrorKind::InvalidData.into()),
            Some(v) => Ok(v),
        }
    }
}

#[derive(Clone)]
struct Hole {
    address: usize,
    size: Size,
    expr: Expr,
    line_num: usize,
    allowed_type: HoleType,
}
impl BinaryWrite for Hole {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.address.bin_write(f)?;
        self.size.bin_write(f)?;
        self.line_num.bin_write(f)?;
        self.expr.bin_write(f)?;
        self.allowed_type.bin_write(f)
    }
}
impl BinaryRead for Hole {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Hole> {
        let address = BinaryRead::bin_read(f)?;
        let size = BinaryRead::bin_read(f)?;
        let line_num = BinaryRead::bin_read(f)?;
        let expr = BinaryRead::bin_read(f)?;
        let allowed_type = BinaryRead::bin_read(f)?;
        Ok(Hole { address, size, line_num, expr, allowed_type })
    }
}

#[derive(Clone)]
pub struct ObjectFile {
    global_symbols: HashMap<String, usize>,
    extern_symbols: HashMap<String, usize>,

    symbols: SymbolTable<usize>,

    text_align: usize,
    rodata_align: usize,
    data_align: usize,
    bss_align: usize,

    text_holes: Vec<Hole>,
    rodata_holes: Vec<Hole>,
    data_holes: Vec<Hole>,

    text: Vec<u8>,
    rodata: Vec<u8>,
    data: Vec<u8>,
    bss_len: usize,
}
const OBJ_PREFIX: &[u8] = "csx64-obj\0".as_bytes();
impl BinaryWrite for ObjectFile {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        OBJ_PREFIX.bin_write(f)?;

        self.global_symbols.bin_write(f)?;
        self.extern_symbols.bin_write(f)?;

        self.symbols.bin_write(f)?;

        self.text_align.bin_write(f)?;
        self.rodata_align.bin_write(f)?;
        self.data_align.bin_write(f)?;
        self.bss_align.bin_write(f)?;

        self.text_holes.bin_write(f)?;
        self.rodata_holes.bin_write(f)?;
        self.data_holes.bin_write(f)?;
        
        self.text.bin_write(f)?;
        self.rodata.bin_write(f)?;
        self.data.bin_write(f)?;
        self.bss_len.bin_write(f)
    }
}
impl BinaryRead for ObjectFile {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<ObjectFile> {
        if Vec::<u8>::bin_read(f)? != OBJ_PREFIX {
            return Err(io::ErrorKind::InvalidData.into());
        }

        let global_symbols = BinaryRead::bin_read(f)?;
        let extern_symbols = BinaryRead::bin_read(f)?;

        let symbols = BinaryRead::bin_read(f)?;

        let text_align = BinaryRead::bin_read(f)?;
        let rodata_align = BinaryRead::bin_read(f)?;
        let data_align = BinaryRead::bin_read(f)?;
        let bss_align = BinaryRead::bin_read(f)?;

        let text_holes = BinaryRead::bin_read(f)?;
        let rodata_holes = BinaryRead::bin_read(f)?;
        let data_holes = BinaryRead::bin_read(f)?;

        let text = BinaryRead::bin_read(f)?;
        let rodata = BinaryRead::bin_read(f)?;
        let data = BinaryRead::bin_read(f)?;
        let bss_len = BinaryRead::bin_read(f)?;

        Ok(ObjectFile {
            global_symbols,
            extern_symbols,

            symbols,

            text_align,
            rodata_align,
            data_align,
            bss_align,

            text_holes,
            rodata_holes,
            data_holes,

            text,
            rodata,
            data,
            bss_len,
        })
    }
}

#[derive(Debug)]
enum RenameError {
    TargetAlreadyExisted,
}
impl ObjectFile {
    /// Renames a symbol in the object file, finding and replacing all instances of identifiers to it.
    /// Note that if the source symbol has already been evaluated it may already be irreversibly folded into other expressions.
    /// This should not be a problem if done to a non-global symbol.
    /// If the source name was not present, does nothing and returns Ok.
    fn rename_symbol(&mut self, from: &str, to: &str) -> Result<(), RenameError> {
        // make sure target name doesn't already exist somewhere (either intern or extern symbol)
        if self.symbols.is_defined(to) || self.extern_symbols.contains_key(to) { return Err(RenameError::TargetAlreadyExisted); }

        // if it's a symbol defined in this file
        if let Some((expr, tag)) = self.symbols.raw.remove(from) {
            self.symbols.define(to.into(), expr, tag).unwrap(); // unwrap is safe because we test if it exists above

            // find and replace in global table (may not be global, that's ok)
            if let Some(tag) = self.global_symbols.remove(from) {
                self.global_symbols.insert(to.into(), tag);
            }
        }
        // if it's a symbol defined externally
        else if let Some(tag) = self.extern_symbols.remove(from) {
            self.extern_symbols.insert(to.into(), tag);
        }

        // now we just have to recursively replace from -> to in every expr in the file
        for (_, (expr, _)) in self.symbols.raw.iter_mut() { rename_symbol_in_expr(expr, from, to); }
        for Hole { expr, .. } in self.text_holes.iter_mut() { rename_symbol_in_expr(expr, from, to); }
        for Hole { expr, .. } in self.rodata_holes.iter_mut() { rename_symbol_in_expr(expr, from, to); }
        for Hole { expr, .. } in self.data_holes.iter_mut() { rename_symbol_in_expr(expr, from, to); }

        Ok(())
    }
    /// Applies the specified renaming transform to all identifiers that are unique to this object file.
    /// This includes all non-global non-extern symbols, as well as segment offsets (but not origins).
    /// This is equivalent to performing a sequence of renaming operations on all internal symbols.
    /// This function will panic if any renaming operation fails.
    /// For correct behavior, the mapping should be injective and never return a symbol that might already be defined.
    /// To this end, it is best practice to only return unique, illegal symbol names, such as `"foo" -> "foo:56"`.
    fn transform_personal_idents<F: Fn(&str) -> String>(&mut self, f: &F) {
        let mut internals: Vec<String> = self.symbols.iter().map(|(sym, _)| sym).filter(|&sym| !self.global_symbols.contains_key(sym)).cloned().collect();

        internals.push(get_seg_offset_str(AsmSegment::Text).into());
        internals.push(get_seg_offset_str(AsmSegment::Rodata).into());
        internals.push(get_seg_offset_str(AsmSegment::Data).into());
        internals.push(get_seg_offset_str(AsmSegment::Bss).into());

        for internal in internals {
            self.rename_symbol(&internal, &f(&internal)).unwrap();
        }
    }
}
fn rename_symbol_in_expr(expr: &mut Expr, from: &str, to: &str) {
    match expr.data.get_mut() {
        ExprData::Value(_) => (),
        ExprData::Ident(ident) => if ident == from { *ident = to.into(); },
        ExprData::Uneval { op: _, left, right } => {
            if let Some(left) = left { rename_symbol_in_expr(left, from, to); }
            if let Some(right) = right { rename_symbol_in_expr(right, from, to); }
        }
    }
}

/// Writes a binary value to the given segment at the specified position.
/// Panics if the range goes out of bounds.
fn segment_write_bin(seg: &mut Vec<u8>, val: &[u8], pos: usize) {
    seg[pos..pos+val.len()].copy_from_slice(val)
}

#[derive(Debug)]
struct PatchError {
    kind: PatchErrorKind,
    line_num: usize,
}
#[derive(Debug)]
enum PatchErrorKind {
    Illegal(IllegalPatchReason),
    NotPatched(EvalError),
}
#[derive(Debug)]
pub enum IllegalPatchReason {
    IllegalExpr(IllegalReason),
    HoleContentInvalidType(HoleType),
    WriteIntegerAsUnsupportedSize(Size),
    WriteFloatAsUnsupportedSize(Size),
    TruncatedSignificantBits,
    TruncatedUTF8,
}

/// Attempts to patch the hole in the given segment.
/// On critical (bad/illegal) failure, returns Err.
/// Otherwise returns Ok(Err) if evaluation fails (this is not a bad error, as it might can be patched later).
/// Returns Ok(OK(())) to denote that everything succeeded and the hole was successfully patched.
fn patch_hole(seg: &mut Vec<u8>, hole: &Hole, symbols: &dyn SymbolTableCore) -> Result<(), PatchError> {
    let val = match hole.expr.eval(symbols) {
        Err(e) => match e {
            EvalError::Illegal(reason) => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::IllegalExpr(reason)), line_num: hole.line_num }),
            EvalError::UndefinedSymbol(_) => return Err(PatchError { kind: PatchErrorKind::NotPatched(e), line_num: hole.line_num }),
        }
        Ok(v) => v,
    };

    match &*val {
        Value::Character(ch) => {
            if hole.allowed_type != HoleType::Integer && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num });
            }
            let mut buf = [0; 4];
            ch.encode_utf8(&mut buf);
            let utf8 = u32::from_le_bytes(buf);
            match hole.size {
                Size::Byte => {
                    if utf8 > u8::MAX as u32 { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedUTF8), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(utf8 as u8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if utf8 > u16::MAX as u32 { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedUTF8), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(utf8 as u16).to_le_bytes(), hole.address)
                }
                Size::Dword => segment_write_bin(seg, &(utf8 as u32).to_le_bytes(), hole.address),
                Size::Qword => segment_write_bin(seg, &(utf8 as u64).to_le_bytes(), hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteIntegerAsUnsupportedSize(x)), line_num: hole.line_num }),
            }
        }
        Value::Integer(v) => {
            if hole.allowed_type != HoleType::Integer && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num });
            }
            match hole.size {
                Size::Byte => match v.to_i8().map(|v| v as u8).or(v.to_u8()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                Size::Word => match v.to_i16().map(|v| v as u16).or(v.to_u16()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                Size::Dword => match v.to_i32().map(|v| v as u32).or(v.to_u32()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                Size::Qword => match v.to_i64().map(|v| v as u64).or(v.to_u64()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteIntegerAsUnsupportedSize(x)), line_num: hole.line_num }),
            }
        }
        Value::Pointer(v) => {
            if hole.allowed_type != HoleType::Pointer && hole.allowed_type != HoleType::Integer && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num });
            }
            match hole.size {
                Size::Byte => {
                    if *v as u8 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as u8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if *v as u16 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as u16).to_le_bytes(), hole.address)
                }
                Size::Dword => {
                    if *v as u32 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as u32).to_le_bytes(), hole.address)
                }
                Size::Qword => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteIntegerAsUnsupportedSize(x)), line_num: hole.line_num }),
            }
        }
        Value::Float(v) => {
            if hole.allowed_type != HoleType::Float && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num });
            }
            match hole.size {
                Size::Dword => segment_write_bin(seg, &v.to_f32().to_le_bytes(), hole.address),
                Size::Qword => segment_write_bin(seg, &v.to_f64().to_le_bytes(), hole.address),
                Size::Tword => segment_write_bin(seg, &F80::from(v).0, hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteFloatAsUnsupportedSize(x)), line_num: hole.line_num }),
            }
        }
        _ => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num }),
    }
    Ok(())
}
fn elim_holes_if_able(seg: &mut Vec<u8>, holes: &mut Vec<Hole>, symbols: &dyn SymbolTableCore) -> Result<(), AsmError> {
    for i in (0..holes.len()).rev() {
        match patch_hole(seg, &holes[i], symbols) {
            Ok(()) => { holes.swap_remove(i); },
            Err(e) => match e.kind {
                PatchErrorKind::NotPatched(_) => (),
                PatchErrorKind::Illegal(r) => return Err(AsmError { kind: AsmErrorKind::IllegalPatch(r), line_num: e.line_num, pos: None, inner_err: None }), // only propagate hard errors
            }
        }
    }
    Ok(())
}
fn elim_all_holes<F: Fn(usize) -> String>(seg: &mut Vec<u8>, holes: &[MergedHole], symbols: &dyn SymbolTableCore, src: &F) -> Result<(), LinkError> {
    for hole in holes {
        match patch_hole(seg, &hole.hole, symbols) {
            Ok(()) => (),
            Err(e) => match e.kind {
                PatchErrorKind::NotPatched(reason) => return Err(LinkError::EvalFailure { src: src(hole.src), line_num: e.line_num, reason }),
                PatchErrorKind::Illegal(reason) => return Err(LinkError::PatchIllegal { src: src(hole.src), line_num: e.line_num, reason }),
            }
        }
    }
    Ok(())
}

fn process_global_extern(arguments: Vec<Argument>, add_to: &mut HashMap<String, usize>, check_in: &HashMap<String, usize>, line_num: usize) -> Result<(), AsmError> {
    if arguments.is_empty() { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCountAtLeast(1), line_num, pos: None, inner_err: None }); }
    for arg in arguments {
        match arg {
            Argument::Imm(v) => {
                if v.size.is_some() { return Err(AsmError { kind: AsmErrorKind::IdentifierHadSizeSpec, line_num, pos: None, inner_err: None }); }
                match v.expr.data.into_inner() {
                    ExprData::Ident(ident) => {
                        debug_assert!(is_valid_symbol_name(&ident) && !is_reserved_symbol_name(&ident));
                        if check_in.contains_key(&ident) { return Err(AsmError { kind: AsmErrorKind::IdentifierIsGlobalAndExtern, line_num, pos: None, inner_err: None }); }
                        if let Some(prev) = add_to.insert(ident, line_num) {
                            return Err(AsmError { kind: AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num: prev }, line_num, pos: None, inner_err: None });
                        }
                    }
                    _ => return Err(AsmError { kind: AsmErrorKind::ExpectedIdentifier, line_num, pos: None, inner_err: None }),
                }
            }
            _ => return Err(AsmError { kind: AsmErrorKind::ExpectedIdentifier, line_num, pos: None, inner_err: None }),
        }
    }
    Ok(())
}

/// Gets the smallest amount of padding needed to align the value.
fn align_off(current: usize, align: usize) -> usize {
    assert!(align.is_power_of_two());
    current.wrapping_neg() & (align - 1)
}
#[test]
fn test_align_off() {
    for v in 0..100 {
        let r = align_off(v, 4);
        assert!(r < 4 && (v + r) % 4 == 0);
    }
}

/// Pads `v` with `count` zeros.
fn pad(v: &mut Vec<u8>, count: usize) {
    v.extend(iter::once(0).cycle().take(count));
}

trait AlignTo {
    fn align_to(&mut self, align: usize);
}
impl AlignTo for Vec<u8> {
    fn align_to(&mut self, align: usize) {
        let off = align_off(self.len(), align);
        pad(self, off);
    }
}
impl AlignTo for usize {
    fn align_to(&mut self, align: usize) {
        let off = align_off(*self, align);
        *self += off;
    }
}

/// Given a segment and a current base alignment, aligns the end to tail_align and updates the base align to be whichever is larger.
fn align_seg<T: AlignTo>(seg: &mut T, seg_align: &mut usize, tail_align: usize) {
    let align = tail_align.max(*seg_align);
    seg.align_to(align);
    *seg_align = align;
}

struct SegmentBases {
    text: usize,
    rodata: usize,
    data: usize,
    bss: usize,
}
#[derive(Clone, Copy)]
struct MergedSymbolTag {
    src: usize,
    line_num: usize 
}
struct MergedHole {
    src: usize,
    hole: Hole,
}

/// The symbols to introduce to the assembler prior to parsing any source.
pub struct Predefines(SymbolTable<usize>);
impl From<SymbolTable<()>> for Predefines {
    /// Constructs a new set of predefines from a symbol table.
    fn from(symbols: SymbolTable<()>) -> Predefines {
        let transformed = symbols.raw.into_iter().map(|(key, (value, _))| (key, (value, 0))).collect();
        Predefines(SymbolTable { raw: transformed })
    }
}
impl Predefines {
    /// Appends the symbols of another symbol table to the list of predefines.
    /// This can be used to define additional symbols on top of the default predefines.
    /// If any new symbol was already defined, returns `Err` with the name of the conflicting symbol.
    /// In the case of an error, `self` is not modified.
    pub fn append(&mut self, symbols: SymbolTable<()>) -> Result<(), String> {
        for key in symbols.raw.keys() {
            if self.0.is_defined(key) {
                return Err(key.clone());
            }
        }
        for (key, (val, _)) in symbols.raw.into_iter() {
            self.0.define(key, val, 0).unwrap();
        }
        Ok(())
    }
}
impl Default for Predefines {
    /// Gets the default predefined symbols
    fn default() -> Predefines {
        let mut symbols: SymbolTable<()> = Default::default();

        symbols.define("sys_exit".to_owned(), (Syscall::Exit as u64).into(), ()).unwrap();
        symbols.define("sys_read".to_owned(), (Syscall::Read as u64).into(), ()).unwrap();
        symbols.define("sys_write".to_owned(), (Syscall::Write as u64).into(), ()).unwrap();
        symbols.define("sys_lseek".to_owned(), (Syscall::Seek as u64).into(), ()).unwrap();
        symbols.define("sys_brk".to_owned(), (Syscall::Break as u64).into(), ()).unwrap();

        Predefines::from(symbols)
    }
}

/// Attempts to assemble the `asm` source file into an `ObjectFile`.
/// It is not required that `asm` be an actual file - it can just be in memory.
/// `asm_name` is the effective name of the source file (the assembly program can access its own file name).
/// It is recommended that `asm_name` be meaningful, as it is might be used by the `asm` program to construct error messages, but this is not required.
pub fn assemble(asm_name: &str, asm: &mut dyn BufRead, predefines: Predefines) -> Result<ObjectFile, AsmError> {
    let mut args = AssembleArgs {
        file_name: asm_name,
        file: ObjectFile {
            global_symbols: Default::default(),
            extern_symbols: Default::default(),

            symbols: predefines.0,

            text_align: 1,
            rodata_align: 1,
            data_align: 1,
            bss_align: 1,

            text_holes: Default::default(),
            rodata_holes: Default::default(),
            data_holes: Default::default(),

            text: Default::default(),
            rodata: Default::default(),
            data: Default::default(),
            bss_len: 0,
        },

        current_seg: None,
        done_segs: Default::default(),

        line_num: 0,
        line_pos_in_seg: 0,

        label_def: None,
        last_nonlocal_label: None,
        
        times: None,
    };

    let mut line = String::new();
    loop {
        line.clear();
        match asm.read_line(&mut line) {
            Err(e) => return Err(AsmError { kind: AsmErrorKind::ReadError(e), line_num: args.line_num, pos: None, inner_err: None }),
            Ok(v) => if v == 0 { break; } // check for EOF
        }
        args.line_num += 1;
        if args.line_num == 1 && line.starts_with("#!") { continue; } // accept a shebang, but only on the first line

        args.update_line_pos_in_seg(); // update line pos prior to parsing the header (times count might refer to current segment position
        let (instruction, header_aft) = args.extract_header(&line)?;
        debug_assert!(match line[header_aft..].chars().next() { Some(c) => c.is_whitespace() || c == COMMENT_CHAR, None => true });
        let (prefix, instruction) = match instruction {
            None => (None, None),
            Some((prefix, instruction)) => (prefix, Some(instruction)), // unpack the prefix/instruction to be easier to work with
        };
        debug_assert!(if prefix.is_some() { instruction.is_some() } else { true }); // this should be guaranteed by the parser

        if let Some((name, _)) = &args.label_def {
            // label on a segment line would be ambiguous where label should go - end of previous segment or start of next
            if let Some((Instruction::SEGMENT, _)) = instruction {
                return Err(AsmError { kind: AsmErrorKind::LabelOnSegmentLine, line_num: args.line_num, pos: None, inner_err: None });
            }

            // equ defines its own symbol, otherwise it's a real label
            match instruction {
                Some((Instruction::EQU, _)) => (),
                _ => {
                    let val = match args.current_seg {
                        None => return Err(AsmError { kind: AsmErrorKind::LabelOutsideOfSegment, line_num: args.line_num, pos: None, inner_err: None }),
                        Some(seg) => {
                            let off = match seg {
                                AsmSegment::Text => args.file.text.len(),
                                AsmSegment::Rodata => args.file.rodata.len(),
                                AsmSegment::Data => args.file.data.len(),
                                AsmSegment::Bss => args.file.bss_len,
                            };
                            Expr::from((OP::Add, ExprData::Ident(get_seg_offset_str(seg).into()), off as i64))
                        }
                    };
                    if let Err(_) = args.file.symbols.define(name.clone(), val, args.line_num) {
                        return Err(AsmError { kind: AsmErrorKind::SymbolAlreadyDefined, line_num: args.line_num, pos: None, inner_err: None });
                    }
                }
            }
        }

        match instruction {
            None => {
                debug_assert!(args.times.is_none()); // this is a syntax error, and should be handled elsewhere
                debug_assert!(prefix.is_none()); // this should be guaranteed by parser
            }
            Some((instruction, instruction_pos)) => {
                debug_assert!(if let Some(TimesInfo { total_count: _, current }) = args.times { current == 0 } else { true }); // if we have times, should start at 0
                loop { // otherwise we have to parse it once each time and update the times iter count after each step (if applicable)
                    if let Some(TimesInfo { total_count, current }) = args.times {
                        debug_assert!(current <= total_count);
                        if current == total_count { break; } // check times exit condition
                    }

                    args.update_line_pos_in_seg(); // update line position once before each first-order iteration
                    let mut arguments = args.extract_arguments(&line, header_aft)?;
                    match prefix { // then we proceed into the handlers
                        Some((Prefix::REP, prefix_pos)) => match instruction {
                            Instruction::MOVS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((1 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::STOS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((8 << 2) | size.basic_sizecode().unwrap()))?,
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForThisInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        Some((Prefix::REPZ, prefix_pos)) => match instruction {
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForThisInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        Some((Prefix::REPNZ, prefix_pos)) => match instruction {
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForThisInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        Some((Prefix::LOCK, prefix_pos)) => match instruction {
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForThisInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        None => match instruction {
                            Instruction::EQU => match &args.label_def {
                                None => return Err(AsmError { kind: AsmErrorKind::EQUWithoutLabel, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }),
                                Some((name, _)) => {
                                    if arguments.len() != 1 {
                                        return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None });
                                    }
                                    let val = match arguments.into_iter().next().unwrap() {
                                        Argument::Imm(imm) => {
                                            if let Some(_) = imm.size {
                                                return Err(AsmError { kind: AsmErrorKind::EQUArgumentHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None });
                                            }
                                            imm.expr
                                        }
                                        _ => return Err(AsmError { kind: AsmErrorKind::ExpectedExpressionArg(0), line_num: args.line_num, pos: None, inner_err: None }),
                                    };
                                    if let Err(_) = args.file.symbols.define(name.clone(), val, args.line_num) {
                                        return Err(AsmError { kind: AsmErrorKind::SymbolAlreadyDefined, line_num: args.line_num, pos: None, inner_err: None });
                                    }
                                }
                            }
                            Instruction::SEGMENT => {
                                if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                let seg = match arguments.into_iter().next().unwrap() {
                                    Argument::Segment(seg) => seg,
                                    _ => return Err(AsmError { kind: AsmErrorKind::ExpectedSegment, line_num: args.line_num, pos: None, inner_err: None }),
                                };
        
                                if args.done_segs.contains(&seg) { return Err(AsmError { kind: AsmErrorKind::SegmentAlreadyCompleted, line_num: args.line_num, pos: None, inner_err: None }); }
                                args.done_segs.push(seg);
                                args.current_seg = Some(seg);
                                args.last_nonlocal_label = None; // we don't want local symbols to propagate accross segments
                                debug_assert!(args.label_def.is_none()); // no labels allowed - should have been taken care of before now
                            }
                            Instruction::GLOBAL => process_global_extern(arguments, &mut args.file.global_symbols, &args.file.extern_symbols, args.line_num)?,
                            Instruction::EXTERN => process_global_extern(arguments, &mut args.file.extern_symbols, &args.file.global_symbols, args.line_num)?,
                            Instruction::ALIGN => {
                                if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                match arguments.into_iter().next().unwrap() {
                                    Argument::Imm(imm) => {
                                        if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::AlignArgumentHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None }); }
                                        let val = match imm.expr.eval(&args.file.symbols) {
                                            Err(_) => return Err(AsmError { kind: AsmErrorKind::AlignValueNotCriticalExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                            Ok(res) => match &*res {
                                                Value::Integer(v) => {
                                                    if v.cmp0() == Ordering::Less { return Err(AsmError { kind: AsmErrorKind::AlignValueNegative, line_num: args.line_num, pos: None, inner_err: None }); }
                                                    match v.to_u64() {
                                                        None => return Err(AsmError { kind: AsmErrorKind::AlignValueExceedsMaxAlign, line_num: args.line_num, pos: None, inner_err: None }),
                                                        Some(v) => v,
                                                    }
                                                }
                                                _ => return Err(AsmError { kind: AsmErrorKind::AlignValueNotInteger, line_num: args.line_num, pos: None, inner_err: None }),
                                            }
                                        };
                                        if val > MAX_ALIGN { return Err(AsmError { kind: AsmErrorKind::AlignValueExceedsMaxAlign, line_num: args.line_num, pos: None, inner_err: None }); }
                                        if !val.is_power_of_two() { return Err(AsmError { kind: AsmErrorKind::AlignValueNotPowerOf2, line_num: args.line_num, pos: None, inner_err: None }); }
                                        let val = val as usize;
                                        debug_assert!(val != 0 && MAX_ALIGN <= usize::MAX as u64 && MAX_ALIGN <= u32::MAX as u64);
        
                                        match args.current_seg {
                                            None => return Err(AsmError { kind: AsmErrorKind::AlignOutsideOfSegment, line_num: args.line_num, pos: None, inner_err: None }),
                                            Some(seg) => match seg {
                                                AsmSegment::Text => align_seg(&mut args.file.text, &mut args.file.text_align, val),
                                                AsmSegment::Rodata => align_seg(&mut args.file.rodata, &mut args.file.rodata_align, val),
                                                AsmSegment::Data => align_seg(&mut args.file.data, &mut args.file.data_align, val),
                                                AsmSegment::Bss => align_seg(&mut args.file.bss_len, &mut args.file.bss_align, val),
                                            }
                                        }
                                    }
                                    _ => return Err(AsmError { kind: AsmErrorKind::AlignValueNotExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                }
                            }
                            Instruction::ASSERT => {
                                if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                let cond = match arguments.into_iter().next().unwrap() {
                                    Argument::Imm(imm) => {
                                        if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::AssertArgHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None }); }
                                        match imm.expr.eval(&args.file.symbols) {
                                            Err(e) => return Err(AsmError { kind: AsmErrorKind::FailedCriticalExpression(e), line_num: args.line_num, pos: None, inner_err: None }),
                                            Ok(res) => match &*res {
                                                Value::Logical(v) => *v,
                                                v => return Err(AsmError { kind: AsmErrorKind::AssertArgNotLogical(v.get_type()), line_num: args.line_num, pos: None, inner_err: None }),
                                            }
                                        }
                                    }
                                    _ => return Err(AsmError { kind: AsmErrorKind::ExpectedExpressionArg(0), line_num: args.line_num, pos: None, inner_err: None }),
                                };
                                if !cond { return Err(AsmError { kind: AsmErrorKind::AssertFailure, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                            }
                            Instruction::DECLARE(size) => {
                                if arguments.len() < 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCountAtLeast(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                for arg in arguments {
                                    match arg {
                                        Argument::Imm(imm) => {
                                            if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::DeclareValueHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None }); }
                                            let handled = match imm.expr.eval(&args.file.symbols) {
                                                Ok(val) => match &*val {
                                                    Value::Binary(content) => {
                                                        if size != Size::Byte { return Err(AsmError { kind: AsmErrorKind::StringDeclareNotByteSize, line_num: args.line_num, pos: None, inner_err: None }); }
                                                        let seg = match args.current_seg {
                                                            Some(seg) => match seg {
                                                                AsmSegment::Text => &mut args.file.text,
                                                                AsmSegment::Rodata => &mut args.file.rodata,
                                                                AsmSegment::Data => &mut args.file.data,
                                                                AsmSegment::Bss => return Err(AsmError { kind: AsmErrorKind::WriteInBssSegment, line_num: args.line_num, pos: None, inner_err: None }),
                                                            }
                                                            None => return Err(AsmError { kind: AsmErrorKind::WriteOutsideOfSegment, line_num: args.line_num, pos: None, inner_err: None }),
                                                        };
                                                        seg.extend_from_slice(content);
                                                        true
                                                    }
                                                    _ => false,
                                                }
                                                Err(_) => false,
                                            };
                                            if !handled { args.append_val(size, imm.expr, HoleType::Any)?; }
                                        }
                                        _ => return Err(AsmError { kind: AsmErrorKind::DeclareValueNotExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                    }
                                }
                            }
                            Instruction::RESERVE(size) => {
                                if args.current_seg != Some(AsmSegment::Bss) { return Err(AsmError { kind: AsmErrorKind::ReserveOutsideOfBss, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                match arguments.into_iter().next().unwrap() {
                                    Argument::Imm(imm) => {
                                        if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::ReserveValueHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None }); }
                                        let count = match imm.expr.eval(&args.file.symbols) {
                                            Err(_) => return Err(AsmError { kind: AsmErrorKind::ReserveValueNotCriticalExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                            Ok(res) => match &*res {
                                                Value::Integer(v) => {
                                                    if v.cmp0() == Ordering::Less { return Err(AsmError { kind: AsmErrorKind::ReserveValueNegative, line_num: args.line_num, pos: None, inner_err: None }); }
                                                    match v.to_u64() {
                                                        None => return Err(AsmError { kind: AsmErrorKind::ReserveValueTooLarge, line_num: args.line_num, pos: None, inner_err: None }),
                                                        Some(v) => v,
                                                    }
                                                }
                                                _ => return Err(AsmError { kind: AsmErrorKind::ReserveValueNotInteger, line_num: args.line_num, pos: None, inner_err: None }),
                                            }
                                        };
                                        if count > usize::MAX as u64 { return Err(AsmError { kind: AsmErrorKind::ReserveValueTooLarge, line_num: args.line_num, pos: None, inner_err: None }); }
                                        let bytes = count as usize * size.size();
                                        args.file.bss_len += bytes;
                                    }
                                    _ => return Err(AsmError { kind: AsmErrorKind::ReserveValueNotExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                }
                            }
        
                            Instruction::NOP => args.process_no_arg_op(arguments, Some(OPCode::NOP as u8), None)?,
                            Instruction::HLT => args.process_no_arg_op(arguments, Some(OPCode::HLT as u8), None)?,
                            Instruction::SYSCALL => args.process_no_arg_op(arguments, Some(OPCode::SYSCALL as u8), None)?,
        
                            Instruction::LFENCE => args.process_no_arg_op(arguments, None, None)?,
                            Instruction::SFENCE => args.process_no_arg_op(arguments, None, None)?,
                            Instruction::MFENCE => args.process_no_arg_op(arguments, None, None)?,
        
                            Instruction::MOV => args.process_binary_op(arguments, OPCode::MOV as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::CMOVcc(ext) => args.process_binary_op(arguments, OPCode::CMOVcc as u8, Some(ext), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::LEA => {
                                if arguments.len() != 2 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[2]), line_num: args.line_num, pos: None, inner_err: None }); }
                                let mut arguments = arguments.into_iter();
        
                                let reg = match arguments.next().unwrap() {
                                    Argument::CPURegister(reg) => {
                                        if reg.size == Size::Byte { return Err(AsmError { kind: AsmErrorKind::LEADestByte, line_num: args.line_num, pos: None, inner_err: None }); }
                                        reg
                                    }
                                    _ => return Err(AsmError { kind: AsmErrorKind::LEADestNotRegister, line_num: args.line_num, pos: None, inner_err: None }),
                                };
                                let addr = match arguments.next().unwrap() {
                                    Argument::Address(addr) => addr,
                                    _ => return Err(AsmError { kind: AsmErrorKind::LEASrcNotAddress, line_num: args.line_num, pos: None, inner_err: None }),
                                };
        
                                args.append_byte(OPCode::LEA as u8)?;
                                args.append_byte((reg.id << 4) | (reg.size.basic_sizecode().unwrap() << 2))?;
                                args.append_address(addr)?;
                            }
                            Instruction::XCHG => args.process_binary_lvalue_unordered_op(arguments, OPCode::XCHG as u8, None, &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?,
                            Instruction::SETcc(ext) => args.process_unary_op(arguments, OPCode::SETcc as u8, Some(ext), &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?,
                            Instruction::FLAGBIT(ext) => args.process_no_arg_op(arguments, Some(OPCode::REGOP as u8), Some(ext))?,

                            Instruction::ADD => args.process_binary_op(arguments, OPCode::ADD as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::SUB => args.process_binary_op(arguments, OPCode::SUB as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::CMP => {
                                let is_cmpz = arguments.len() == 2 && match &arguments[1] {
                                    Argument::Imm(imm) => match imm.expr.eval(&args.file.symbols) {
                                        Ok(v) => match &*v {
                                            Value::Integer(v) => v.cmp0() == Ordering::Equal,
                                            Value::Pointer(v) => *v == 0,
                                            _ => false,
                                        }
                                        Err(_) => false,
                                    }
                                    _ => false,
                                };
                                if is_cmpz {
                                    arguments.pop();
                                    args.process_unary_op(arguments, OPCode::CMPZ as u8, None, &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?
                                }
                                else { args.process_binary_op(arguments, OPCode::CMP as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)? }
                            }
        
                            Instruction::AND => args.process_binary_op(arguments, OPCode::AND as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::OR => args.process_binary_op(arguments, OPCode::OR as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::XOR => args.process_binary_op(arguments, OPCode::XOR as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::TEST => args.process_binary_op(arguments, OPCode::TEST as u8, None, HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
        
                            Instruction::SHIFT(ext) => args.process_binary_op(arguments, OPCode::BITWISE as u8, Some(ext), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], Some(Size::Byte), Some(Size::Byte))?,
                            Instruction::SHIFTX(ext) => args.process_ternary_op(arguments, OPCode::BITWISE as u8, Some(ext), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, Some(Size::Byte))?,
                            Instruction::BTX(ext) => args.process_binary_op(arguments, OPCode::BITWISE as u8, Some(ext), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, Some(Size::Byte))?,

                            Instruction::MUL => match arguments.len() {
                                1 => args.process_value_op(arguments, OPCode::MULDIV as u8, Some(0), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None)?,
                                2 => args.process_binary_op(arguments, OPCode::MULDIV as u8, Some(1), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                                3 => args.process_ternary_op(arguments, OPCode::MULDIV as u8, Some(2), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                                _ => return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1, 2, 3]), line_num: args.line_num, pos: None, inner_err: None }),
                            }
                            Instruction::IMUL => match arguments.len() {
                                1 => args.process_value_op(arguments, OPCode::MULDIV as u8, Some(4), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None)?,
                                2 => args.process_binary_op(arguments, OPCode::MULDIV as u8, Some(5), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                                3 => args.process_ternary_op(arguments, OPCode::MULDIV as u8, Some(6), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                                _ => return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1, 2, 3]), line_num: args.line_num, pos: None, inner_err: None }),
                            }
                            Instruction::MULX => args.process_ternary_op(arguments, OPCode::MULDIV as u8, Some(3), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::IMULX => args.process_ternary_op(arguments, OPCode::MULDIV as u8, Some(7), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None, None)?,
                            Instruction::DIV => args.process_value_op(arguments, OPCode::MULDIV as u8, Some(8), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None)?,
                            Instruction::IDIV => args.process_value_op(arguments, OPCode::MULDIV as u8, Some(9), HoleType::Integer, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None)?,

                            Instruction::JMP => args.process_value_op(arguments, OPCode::JMP as u8, None, HoleType::Integer, &[Size::Word, Size::Dword, Size::Qword], Some(Size::Qword))?,
                            Instruction::Jcc(ext) => args.process_value_op(arguments, OPCode::Jcc as u8, Some(ext), HoleType::Integer, &[Size::Word, Size::Dword, Size::Qword], Some(Size::Qword))?,
                            Instruction::LOOPcc(ext) => args.process_value_op(arguments, OPCode::LOOPcc as u8, Some(ext), HoleType::Integer, &[Size::Word, Size::Dword, Size::Qword], Some(Size::Qword))?,
                            Instruction::CALL => args.process_value_op(arguments, OPCode::CALL as u8, None, HoleType::Integer, &[Size::Word, Size::Dword, Size::Qword], Some(Size::Qword))?,
                            Instruction::RET => args.process_no_arg_op(arguments, Some(OPCode::RET as u8), None)?,

                            Instruction::PUSH => args.process_value_op(arguments, OPCode::PUSH as u8, None, HoleType::Integer, &[Size::Word, Size::Dword, Size::Qword], None)?,
                            Instruction::POP => args.process_unary_op(arguments, OPCode::POP as u8, None, &[Size::Word, Size::Dword, Size::Qword])?,

                            Instruction::INC => args.process_unary_op(arguments, OPCode::INC as u8, None, &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?,
                            Instruction::DEC => args.process_unary_op(arguments, OPCode::DEC as u8, None, &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?,
                            Instruction::NEG => args.process_unary_op(arguments, OPCode::NEG as u8, None, &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?,
                            Instruction::NOT => args.process_unary_op(arguments, OPCode::NOT as u8, None, &[Size::Byte, Size::Word, Size::Dword, Size::Qword])?,

                            Instruction::MOVS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((0 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::STOS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((7 << 2) | size.basic_sizecode().unwrap()))?,
                            
                            Instruction::FINIT => args.process_no_arg_op(arguments, Some(OPCode::FINIT as u8), None)?,

                            Instruction::FLD(int) => args.process_fpu_value_op(arguments, OPCode::FLD as u8, None, int)?,

                            Instruction::FADD(int, pop) => args.process_fpu_binary_op(arguments, OPCode::FADD as u8, None, int, pop)?,
                            Instruction::FSUB(int, pop) => args.process_fpu_binary_op(arguments, OPCode::FSUB as u8, None, int, pop)?,
                            Instruction::FSUBR(int, pop) => args.process_fpu_binary_op(arguments, OPCode::FSUBR as u8, None, int, pop)?,
                            
                            Instruction::DEBUG(ext) => args.process_no_arg_op(arguments, Some(OPCode::DEBUG as u8), Some(ext))?,
                        }
                    }
        
                    match &mut args.times { // update times count if applicable, otherwise break on no times count
                        None => break,
                        Some(info) => info.current += 1,
                    }
                }
            }
        }

        // if we defined a non-local symbol, add it after we finish assembling that line (locals in this line should refer to past parent)
        if let Some((symbol, Locality::Nonlocal)) = args.label_def.take() { // we can take it since we're about to blow it up on next pass anyway
            args.last_nonlocal_label = Some(symbol);
        }
    }

    // link each symbol to internal symbols (minimizes file size and allows us to eliminate resolved internals)
    for (_, (expr, line_num)) in args.file.symbols.iter() {
        if let Err(EvalError::Illegal(reason)) = expr.eval(&args.file.symbols) {
            return Err(AsmError { kind: AsmErrorKind::ExprIllegalError(reason), line_num: *line_num, pos: None, inner_err: None });
        }
    }

    // eliminate all the holes we can and test for static errors
    elim_holes_if_able(&mut args.file.text, &mut args.file.text_holes, &args.file.symbols)?;
    elim_holes_if_able(&mut args.file.rodata, &mut args.file.rodata_holes, &args.file.symbols)?;
    elim_holes_if_able(&mut args.file.data, &mut args.file.data_holes, &args.file.symbols)?;

    // now we just need to do the final soundness verifications and return the result
    args.finalize()
}
/// Attempts to link one or more (named) object files into an executable.
/// The first object file, `objs[0]` is known as the "start file".
/// The start file's text segment (starting at the beginning) is the first thing to execute upon running the resulting executable.
/// For very basic programs this is fine, but using a higher-level framework might require setup prior to running the "main" logic.
/// Typically, this is denoted by a generic symbol such as "start" (hence, start file).
/// If `entry_point` is `Some((from, to))`, the linker will perform a renaming operation for identifiers in the start file (only).
/// For example, a typical C-like program would use `Some(("start", "main"))` - any occurence of `start` would be replaced by `main`.
pub fn link(mut objs: Vec<(String, ObjectFile)>, entry_point: Option<(&str, &str)>) -> Result<Executable, LinkError> {
    if objs.is_empty() { return Err(LinkError::NothingToLink); }

    // if an entry point was specified, perform the replacement
    if let Some((from, to)) = entry_point {
        if !objs[0].1.extern_symbols.contains_key(from) { return Err(LinkError::EntryPointSourceNotExtern); }

        if !is_valid_symbol_name(to) { return Err(LinkError::EntryPointTargetNotValidIdent); }
        if is_reserved_symbol_name(to) { return Err(LinkError::EntryPointTargetWasReservedSymbol); }

        match objs[0].1.rename_symbol(from, to) {
            Ok(()) => (),
            Err(e) => match e {
                RenameError::TargetAlreadyExisted => return Err(LinkError::EntryPointTargetAlreadyExisted),
            }
        }
    }
    let is_entry_point = |s: &str| match entry_point {
        None => false,
        Some((_, p)) => p == s,
    };

    // map all global symbols to their index in objs array - handle duplicate exports
    let mut global_to_obj: HashMap<String, usize> = Default::default();
    for (i, obj) in objs.iter().enumerate() {
        for (global, &here_line) in obj.1.global_symbols.iter() {
            if let Some(there_line) = global_to_obj.insert(global.into(), i) {
                return Err(LinkError::GlobalSymbolMultipleSources { ident: global.into(), src1: (objs[there_line].0.to_owned(), there_line), src2: (obj.0.to_owned(), here_line) });
            }
        }
    }

    // locations for merged segments
    let mut text = vec![];
    let mut rodata = vec![];
    let mut data = vec![];
    let mut bss_len = 0;

    // total alignments of merged segments
    let mut text_align = 1;
    let mut rodata_align = 1;
    let mut data_align = 1;
    let mut bss_align = 1;

    let mut merged_symbols: SymbolTable<MergedSymbolTag> = SymbolTable::new();
    let mut merged_text_holes: Vec<MergedHole> = vec![];
    let mut merged_rodata_holes: Vec<MergedHole> = vec![];
    let mut merged_data_holes: Vec<MergedHole> = vec![];

    let mut included: HashMap<usize, SegmentBases> = Default::default(); // maps included files to their segment bases in the result
    let mut include_queue: VecDeque<usize> = Default::default();
    include_queue.push_back(0); // we always start with the start file (first object file)
    while let Some(obj_index) = include_queue.pop_front() {
        let (obj_name, obj) = &mut objs[obj_index];

        // account for alignment requirements
        align_seg(&mut text, &mut text_align, obj.text_align);
        align_seg(&mut rodata, &mut rodata_align, obj.rodata_align);
        align_seg(&mut data, &mut data_align, obj.data_align);
        align_seg(&mut bss_len, &mut bss_align, obj.bss_align);

        // grab segment bases, use them to fix the hole positions, and mark this object file as included
        let bases = SegmentBases { text: text.len(), rodata: rodata.len(), data: data.len(), bss: bss_len };
        for hole in obj.text_holes.iter_mut() { hole.address += bases.text; }
        for hole in obj.rodata_holes.iter_mut() { hole.address += bases.rodata; }
        for hole in obj.data_holes.iter_mut() { hole.address += bases.data; }
        assert!(included.insert(obj_index, bases).is_none());

        // merge the segments
        text.extend_from_slice(&obj.text);
        rodata.extend_from_slice(&obj.rodata);
        data.extend_from_slice(&obj.data);
        bss_len += obj.bss_len;

        // mutate all the non-global and non-extern identifiers to be unique before we merge them into the combined symbol table
        obj.transform_personal_idents(&|s| format!("{}:{}", s, obj_index)); // ':' is not a legal symbol char, so guaranteed to not be taken

        // merge all the symbols and holes
        for (sym, (expr, line_num)) in mem::take(&mut obj.symbols).raw {
            merged_symbols.define(sym, expr, MergedSymbolTag { src: obj_index, line_num }).unwrap();
        }
        for hole in mem::take(&mut obj.text_holes) { merged_text_holes.push(MergedHole { src: obj_index, hole }) }
        for hole in mem::take(&mut obj.rodata_holes) { merged_rodata_holes.push(MergedHole { src: obj_index, hole }) }
        for hole in mem::take(&mut obj.data_holes) { merged_data_holes.push(MergedHole { src: obj_index, hole }) }

        // for any external symbol we have, schedule the (single) associated object file defining it for inclusion
        for (req, _) in obj.extern_symbols.iter() {
            match global_to_obj.get(req) {
                None => match is_entry_point(req) {
                    false => return Err(LinkError::ExternSymbolNotDefined { ident: req.to_owned(), required_by: obj_name.to_owned() }),
                    true => return Err(LinkError::EntryPointTargetNotDefined),
                }
                Some(other_index) => if !included.contains_key(other_index) && !include_queue.contains(other_index) {
                    include_queue.push_back(*other_index); // only schedule for inclusion if not already included and not already scheduled
                }
            }
        }
    }

    // merge all the binaries together - these are stored in expressions throughout the symbol table and the various segment holes
    let mut binaries = BinarySet::new();
    fn resolve_binaries(src: &str, line_num: usize, expr: &mut ExprData, binaries: &mut BinarySet, symbols: &SymbolTable<MergedSymbolTag>) -> Result<(), LinkError> {
        match expr {
            ExprData::Value(_) => (),
            ExprData::Ident(_) => (),
            ExprData::Uneval { op: OP::Memory, left, right } => {
                if let Some(_) = right.as_ref() { panic!("expr unary op node had a right branch"); }
                macro_rules! handle_content {
                    ($self:ident, $v:expr) => {
                        match $v {
                            Value::Binary(content) => match content.is_empty() {
                                true => 0u64.into(), // empty binary is mapped to null - we are only required to make sure the content is equal, but there was no content
                                false => {
                                    let idx = binaries.add(Cow::from(content));
                                    ExprData::Ident(format!("{}{:x}", BINARY_LITERAL_SYMBOL_PREFIX, idx)) // good binary is mapped to a unique key in the merged symbol table
                                }
                            }
                            a => return Err(LinkError::EvalFailure { src: src.into(), line_num, reason: IllegalReason::IncompatibleType(OP::Memory, a.get_type()).into() }),
                        }
                    }
                }
                let res: ExprData = match left.take().expect("expr unary op node was missing the left branch").into_eval(symbols) {
                    Err(e) => return Err(LinkError::EvalFailure { src: src.into(), line_num, reason: e }),
                    Ok(val) => match val {
                        ValueCow::Owned(v) => handle_content!(self, v),
                        ValueCow::Borrowed(v) => handle_content!(self, &*v),
                    }
                };
                *expr = res;
            }
            ExprData::Uneval { left, right, .. } => {
                if let Some(left) = left { resolve_binaries(src, line_num, left.data.get_mut(), binaries, symbols)? }
                if let Some(right) = right { resolve_binaries(src, line_num, right.data.get_mut(), binaries, symbols)? }
            }
        }
        Ok(())
    }
    for (_, (expr, tag)) in merged_symbols.iter() {
        resolve_binaries(&objs[tag.src].0, tag.line_num, &mut *expr.data.borrow_mut(), &mut binaries, &merged_symbols)?
    }
    for hole in merged_text_holes.iter_mut().chain(merged_rodata_holes.iter_mut()).chain(merged_data_holes.iter_mut()) {
        resolve_binaries(&objs[hole.src].0, hole.hole.line_num, hole.hole.expr.data.get_mut(), &mut binaries, &merged_symbols)?
    }

    // after merging, but before alignment, we need to allocate all the provisioned binary constants we just handled
    let (backing_bin, slice_bin) = binaries.decompose();
    let mut rodata_backing_bin_offsets: Vec<usize> = Vec::with_capacity(backing_bin.len());
    for backing in backing_bin.iter() {
        rodata_backing_bin_offsets.push(rodata.len()); // keep track of insertion point
        rodata.extend_from_slice(backing); // insert into rodata segment
    }

    // account for segment alignments so we can start taking absolute addresses
    { let s = text.len();                             pad(&mut text, align_off(s, rodata_align)); }
    { let s = text.len() + rodata.len();              pad(&mut rodata, align_off(s, data_align)); }
    { let s = text.len() + rodata.len() + data.len(); pad(&mut text, align_off(s, rodata_align)); }
    let illegal_tag = MergedSymbolTag { src: !0, line_num: !0 }; // we use this tag for things that will always succeed

    // now we can go ahead and resolve all the missing binaries with absolute addresses in rodata
    for (i, slice) in slice_bin.iter().enumerate() {
        let pos = text.len() + rodata_backing_bin_offsets[slice.src] + slice.start;
        assert!(pos >= text.len() && pos < text.len() + rodata.len() && pos + slice.length <= text.len() + rodata.len()); // sanity check - make sure it's in the rodata segment
        merged_symbols.define(format!("{}{:x}", BINARY_LITERAL_SYMBOL_PREFIX, i), pos.into(), illegal_tag).unwrap();
    }

    // define segment origins
    merged_symbols.define(get_seg_origin_str(AsmSegment::Text).into(), Value::Pointer(0).into(), illegal_tag).unwrap();
    merged_symbols.define(get_seg_origin_str(AsmSegment::Rodata).into(), Value::Pointer(text.len() as u64).into(), illegal_tag).unwrap();
    merged_symbols.define(get_seg_origin_str(AsmSegment::Data).into(), Value::Pointer((text.len() + rodata.len()) as u64).into(), illegal_tag).unwrap();
    merged_symbols.define(get_seg_origin_str(AsmSegment::Bss).into(), Value::Pointer((text.len() + rodata.len() + data.len()) as u64).into(), illegal_tag).unwrap();

    // define segment offsets
    for (&obj_index, bases) in included.iter() {
        merged_symbols.define(format!("{}:{}", get_seg_offset_str(AsmSegment::Text), obj_index), Value::Pointer(bases.text as u64).into(), illegal_tag).unwrap();
        merged_symbols.define(format!("{}:{}", get_seg_offset_str(AsmSegment::Rodata), obj_index), Value::Pointer((text.len() + bases.rodata) as u64).into(), illegal_tag).unwrap();
        merged_symbols.define(format!("{}:{}", get_seg_offset_str(AsmSegment::Data), obj_index), Value::Pointer((text.len() + rodata.len() + bases.data) as u64).into(), illegal_tag).unwrap();
        merged_symbols.define(format!("{}:{}", get_seg_offset_str(AsmSegment::Bss), obj_index), Value::Pointer((text.len() + rodata.len() + data.len() + bases.bss) as u64).into(), illegal_tag).unwrap();
    }

    // patch all the holes in each segment
    let get_src_name = |src: usize| objs[src].0.to_owned();
    elim_all_holes(&mut text, &merged_text_holes, &merged_symbols, &get_src_name)?;
    elim_all_holes(&mut rodata, &merged_rodata_holes, &merged_symbols, &get_src_name)?;
    elim_all_holes(&mut data, &merged_data_holes, &merged_symbols, &get_src_name)?;

    // make sure all symbols were evaluated - not strictly necessary, but it would be bad practice to permit them
    for (_, (expr, tag)) in merged_symbols.iter() {
        if let Err(e) = expr.eval(&merged_symbols) {
            return Err(LinkError::EvalFailure { src: objs[tag.src].0.to_owned(), line_num: tag.line_num, reason: e });
        }
    }

    // combine the segments together into final content and we're practically done
    let mut content = Vec::with_capacity(text.len() + rodata.len() + data.len());
    content.extend_from_slice(&text);
    content.extend_from_slice(&rodata);
    content.extend_from_slice(&data);

    Ok(Executable {
        text_seglen: text.len(),
        rodata_seglen: rodata.len(),
        data_seglen: data.len(),
        bss_seglen: bss_len,
        content,
    })
}

lazy_static! {
    static ref STDLIB: Vec<(&'static str, Vec<u8>)> = {
        macro_rules! assemble_physical_file {
            ($name:literal) => {{
                let obj = assemble($name, &mut include_str!(concat!("../asm/stdlib/", $name)).as_bytes(), Default::default()).unwrap();
                let mut bin = vec![];
                obj.bin_write(&mut bin).unwrap();
                ($name, bin)
            }}
        }
        vec![
            assemble_physical_file!("start.asm"),
            assemble_physical_file!("malloc.asm"),
            assemble_physical_file!("exit.asm"),
            assemble_physical_file!("ctype.asm"),
        ]
    };
}
/// Gets a copy of the C-style standard library object files for use in CSX64 asm programs.
/// Notably, this includes the start file which is required by the linker to use entry points.
/// The standard library includes tools such as `malloc`, `free`, `printf`, etc.
/// 
/// If you wish to link one or more object files to the standard library, call this function and append your object files to the end.
/// The whole sequence can then be handed over to the linker, which will ensure that only the files that were reference are included in the result.
pub fn stdlib() -> Vec<(String, ObjectFile)> {
    STDLIB.iter().map(|(name, bin)| (name.to_string(), ObjectFile::bin_read(&mut bin.as_slice()).unwrap())).collect()
}