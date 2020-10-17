//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{self, Read, Write, BufRead};
use std::{mem, iter};

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
use crate::common::{OPCode, Executable};

/// The kinds of errors that can occur during assembly.
/// These are meant to be specific enough to have customized, detailed error messages.
#[derive(Debug)]
pub enum AsmErrorKind {
    /// A read error occurred, which cause assembly to halt prematurely.
    ReadError(io::Error),

    // --------------------------------------------------------------------------

    /// Incorrect number of arguments supplied. Expected this many.
    ArgsExpectedCount(u8),
    /// Incorrect number of arguments supplied. Expected at least this many.
    ArgsExpectedCountAtLeast(u8),
    /// There was unknown content after the arguments list.
    ExtraContentAfterArgs,

    // --------------------------------------------------------------------------

    /// A global symbol was defined in terms of an external symbol.
    GlobalUsesExtern { extern_sym: String },

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
    IllFormedExpr,

    IllFormedNumericLiteral,
    NumericLiteralWithZeroPrefix,
    
    LocalSymbolBeforeNonlocal,
    InvalidSymbolName,
    ReservedSymbolName,

    ExpectedBinaryValue,
    EmptyBinaryValue,

    LabelOutsideOfSegment,
    SymbolAlreadyDefined,
    IllegalInCurrentSegment,
    TimesIterOutisideOfTimes,

    ExpectedAddress,
    UnterminatedAddress,
    AddressSizeMissingPtr,
    AddressRegMultNotCriticalExpr,
    AddressRegMultNotSignedInt,
    AddressRegInvalidMult,
    AddressRegIllegalOp,
    AddressConflictingSizes,
    AddressTooManyRegs,
    AddressSizeUnsupported,
    AddressTypeUnsupported,
    AddressInteriorNotSingleExpr,
    AddressPtrSpecWithoutSize,
    AddressSizeNotRecognized,
    AddressUseOfHighRegister,

    FailedParseImm,
    FailedParseAddress,
    FailedParseCPURegister,
    FailedParseFPURegister,
    FailedParseVPURegister,

    RegisterWithSizeSpec,
    
    TimesMissingCount,
    TimesCountNotImm,
    TimesCountHadSizeSpec,
    TimesCountNotCriticalExpression,
    TimesCountNotInteger,
    TimesCountWasNegative,
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
    SizeSpecOnForcedSize,
    BinaryOpUnsupportedSrcDestTypes, // e.g. memory x memory
    CouldNotDeduceOperandSize,

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

    GlobalSymbolWasNotDefined,
    UnknownSymbol,
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

    GlobalSymbolMultipleSources { ident: String, src1: (String, usize), src2: (String, usize) },
    ExternSymbolNotDefined { ident: String, required_by: String },

    GlobalExprIllegal { src: String, ident: String, reason: IllegalReason },
    
    PatchEvalFailure { src: String, line_num: usize, reason: EvalError },
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
enum Argument {
    CPURegister(CPURegisterInfo),
    FPURegister(FPURegisterInfo),
    VPURegister(VPURegisterInfo),
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
    /// If elf is a basic size (byte, word, dword, qword), returns the size (1, 2, 4, 8).
    fn basic_size(self) -> Option<u8> {
        self.basic_sizecode().map(|v| 1 << v)
    }

    /// If self is a vector size (xmmword, ymmword, zmmword), returns the sizecode (0, 1, 2)
    fn vector_sizecode(self) -> Option<u8> {
        match self {
            Size::Xword => Some(0),
            Size::Yword => Some(1),
            Size::Zword => Some(2),
            _ => None
        }
    }
    /// If self is a vector size (xmmword, ymmword, zmmword), return the size (16, 32, 64).
    fn vector_size(self) -> Option<u8> {
        self.vector_sizecode().map(|v| 1 << (v + 4))
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
    assert_eq!(Size::Dword.basic_size(), Some(4));
    assert_eq!(Size::Dword.vector_size(), None);
    assert_eq!(Size::Xword.basic_sizecode(), None);
    assert_eq!(Size::Xword.vector_sizecode(), Some(0));
    assert_eq!(Size::Xword.vector_size(), Some(16));
    assert_eq!(Size::Yword.vector_sizecode(), Some(1));
    assert_eq!(Size::Yword.vector_size(), Some(32));
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HoleType {
    Signed,
    Unsigned,
    Pointer,
    Integral, // signed, unsigned, or pointer
    Floating,
    Any, // anything goes (used for e.g. dd)
}
impl BinaryWrite for HoleType {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            HoleType::Signed => 0u8,
            HoleType::Unsigned => 1u8,
            HoleType::Pointer => 2u8,
            HoleType::Integral => 3u8,
            HoleType::Floating => 4u8,
            HoleType::Any => 5u8,
        }.bin_write(f)
    }
}
impl BinaryRead for HoleType {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<HoleType> {
        Ok(match u8::bin_read(f)? {
            0 => HoleType::Signed,
            1 => HoleType::Unsigned,
            2 => HoleType::Pointer,
            3 => HoleType::Integral,
            4 => HoleType::Floating,
            5 => HoleType::Any,
            _ => return Err(io::ErrorKind::InvalidData.into())
        })
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
    binary_set: BinarySet,

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
        self.bss_len.bin_write(f)?;

        self.binary_set.bin_write(f)
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

        let binary_set = BinaryRead::bin_read(f)?;

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

            binary_set,
        })
    }
}

#[derive(Debug)]
enum RenameError {
    TargetAlreadyExisted,
    SourceWasAlreadyEvaluated,
    SourceDidNotExist,
}
impl ObjectFile {
    fn rename_symbol(&mut self, from: &str, to: &str) -> Result<(), RenameError> {
        // make sure target name doesn't already exist somewhere (either intern or extern symbol)
        if self.symbols.is_defined(to) || self.extern_symbols.contains_key(to) { return Err(RenameError::TargetAlreadyExisted); }

        // if it's a symbol defined in this file
        if let Some((expr, tag)) = self.symbols.raw.remove(from) {
            if let ExprData::Value(_) = &*expr.data.borrow() {
                return Err(RenameError::SourceWasAlreadyEvaluated); // make sure it hasn't already been evaluated (because it may have already been linked to other expressions)
            }

            // rename the symbol
            self.symbols.define(to.to_owned(), expr, tag).unwrap(); // unwrap is safe because we test if it exists above

            // find and replace in global table (may not be global, that's ok)
            if let Some(tag) = self.global_symbols.remove(from) {
                self.global_symbols.insert(to.into(), tag);
            }
        }
        // if it's a symbol defined externally
        else if let Some(tag) = self.extern_symbols.remove(from) {
            self.extern_symbols.insert(to.into(), tag);
        }
        // otherwise we don't know what it is
        else { return Err(RenameError::SourceDidNotExist); }

        // now we just have to recursively replace from -> to in every expr in the file
        for (_, (expr, _)) in self.symbols.raw.iter_mut() { rename_symbol_in_expr(expr, from, to); }
        for Hole { expr, .. } in self.text_holes.iter_mut() { rename_symbol_in_expr(expr, from, to); }
        for Hole { expr, .. } in self.rodata_holes.iter_mut() { rename_symbol_in_expr(expr, from, to); }
        for Hole { expr, .. } in self.data_holes.iter_mut() { rename_symbol_in_expr(expr, from, to); }

        Ok(())
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
    HoleContentInvalidType(HoleType),
    WriteIntegerAsUnsupportedSize(Size),
    WriteFloatAsUnsupportedSize(Size),
    TruncatedSignificantBits,
}

/// Attempts to patch the hole in the given segment.
/// On critical (bad/illegal) failure, returns Err.
/// Otherwise returns Ok(Err) if evaluation fails (this is not a bad error, as it might can be patched later).
/// Returns Ok(OK(())) to denote that everything succeeded and the hole was successfully patched.
fn patch_hole(seg: &mut Vec<u8>, hole: &Hole, symbols: &dyn SymbolTableCore) -> Result<(), PatchError> {
    let val = match hole.expr.eval(symbols) {
        Err(e) => return Err(PatchError { kind: PatchErrorKind::NotPatched(e), line_num: hole.line_num }),
        Ok(v) => v,
    };

    match &*val {
        Value::Signed(v) => {
            if hole.allowed_type != HoleType::Signed && hole.allowed_type != HoleType::Integral {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num });
            }
            match hole.size {
                Size::Byte => {
                    if *v as i8 as i64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if *v as i16 as i64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as i16).to_le_bytes(), hole.address)
                }
                Size::Dword => {
                    if *v as i32 as i64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as i32).to_le_bytes(), hole.address)
                }
                Size::Qword => segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteIntegerAsUnsupportedSize(x)), line_num: hole.line_num }),
            }
        }
        Value::Unsigned(v) | Value::Pointer(v) => {
            if hole.allowed_type != HoleType::Unsigned && hole.allowed_type != HoleType::Integral {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type)), line_num: hole.line_num });
            }
            match hole.size {
                Size::Byte => {
                    if *v as u8 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if *v as u16 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Dword => {
                    if *v as u32 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Qword => segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteIntegerAsUnsupportedSize(x)), line_num: hole.line_num }),
            }
        }
        Value::Floating(v) => {
            if hole.allowed_type != HoleType::Floating {
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
fn elim_all_holes(src: &str, seg: &mut Vec<u8>, holes: &[Hole], symbols: &dyn SymbolTableCore) -> Result<(), LinkError> {
    for hole in holes {
        match patch_hole(seg, hole, symbols) {
            Ok(()) => (),
            Err(e) => match e.kind {
                PatchErrorKind::NotPatched(reason) => return Err(LinkError::PatchEvalFailure { src: src.into(), line_num: e.line_num, reason }),
                PatchErrorKind::Illegal(reason) => return Err(LinkError::PatchIllegal { src: src.into(), line_num: e.line_num, reason }),
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
                            return Err(AsmError { kind: AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num: line_num }, line_num, pos: None, inner_err: None });
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

#[derive(Debug, Clone, Copy)]
struct SegmentBases {
    text: usize,
    rodata: usize,
    data: usize,
    bss: usize,
}

/// Attempts to assemble the `asm` source file into an `ObjectFile`.
/// It is not required that `asm` be an actual file - it can just be in memory.
/// `asm_name` is the effective name of the source file (the assembly program can access its own file name).
/// It is recommended that `asm_name` be meaningful, as it is might be used by the `asm` program to construct error messages, but this is not required.
pub fn assemble(asm_name: &str, asm: &mut dyn BufRead, predefines: SymbolTable<usize>) -> Result<ObjectFile, AsmError> {
    let mut args = AssembleArgs {
        file_name: asm_name,
        file: ObjectFile {
            global_symbols: Default::default(),
            extern_symbols: Default::default(),

            symbols: predefines,
            binary_set: Default::default(),

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
            Ok(v) => if v == 0 { break; }
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

        // if times count is zero, we shouldn't even look at the rest of the line
        let (instruction, instruction_pos) = match instruction {
            None => {
                debug_assert!(args.times.is_none()); // this is a syntax error, and should be handled elsewhere
                debug_assert!(prefix.is_none()); // this should be guaranteed by parser
                continue; // if there's not an instruction on this line, we also don't have to do anything
            }
            Some(x) => x,
        };
        if let Some(TimesInfo { total_count: 0, current: _ }) = args.times { continue; }
        loop { // otherwise we have to parse it once each time and update the times iter count after each step (if applicable)
            args.update_line_pos_in_seg(); // update line position once before each first-order iteration
            let arguments = args.extract_arguments(&line, header_aft)?;
            match prefix { // then we proceed into the handlers
                Some((Prefix::REP, prefix_pos)) => match instruction {
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
                                return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None });
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
                            if let Err(_) = args.file.symbols.define(name.into(), val, args.line_num) {
                                return Err(AsmError { kind: AsmErrorKind::SymbolAlreadyDefined, line_num: args.line_num, pos: None, inner_err: None });
                            }
                        }
                    }
                    Instruction::SEGMENT => {
                        if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
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
                        if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                        match arguments.into_iter().next().unwrap() {
                            Argument::Imm(imm) => {
                                if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::AlignArgumentHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None }); }
                                let val = match imm.expr.eval(&args.file.symbols) {
                                    Err(_) => return Err(AsmError { kind: AsmErrorKind::AlignValueNotCriticalExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                    Ok(res) => match &*res {
                                        Value::Signed(v) => {
                                            if *v < 0 { return Err(AsmError { kind: AsmErrorKind::AlignValueNegative, line_num: args.line_num, pos: None, inner_err: None }); }
                                            *v as u64
                                        }
                                        Value::Unsigned(v) => *v,
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
                        if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
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
                                    args.append_val(size, imm.expr, HoleType::Any)?;
                                }
                                _ => return Err(AsmError { kind: AsmErrorKind::DeclareValueNotExpr, line_num: args.line_num, pos: None, inner_err: None }),
                            }
                        }
                    }
                    Instruction::RESERVE(size) => {
                        if args.current_seg != Some(AsmSegment::Bss) { return Err(AsmError { kind: AsmErrorKind::ReserveOutsideOfBss, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                        if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                        match arguments.into_iter().next().unwrap() {
                            Argument::Imm(imm) => {
                                if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::ReserveValueHadSizeSpec, line_num: args.line_num, pos: None, inner_err: None }); }
                                let count = match imm.expr.eval(&args.file.symbols) {
                                    Err(_) => return Err(AsmError { kind: AsmErrorKind::ReserveValueNotCriticalExpr, line_num: args.line_num, pos: None, inner_err: None }),
                                    Ok(res) => match &*res {
                                        Value::Signed(v) => {
                                            if *v < 0 { return Err(AsmError { kind: AsmErrorKind::ReserveValueNegative, line_num: args.line_num, pos: None, inner_err: None }); }
                                            *v as u64
                                        }
                                        Value::Unsigned(v) => *v,
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

                    Instruction::MOV => args.process_binary_op(arguments, OPCode::MOV as u8, None, HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None)?,
                    Instruction::MOVcc(ext) => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(ext), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None)?,
                }
            }

            match &mut args.times { // update times count if applicable (and test for break condition)
                None => break,
                Some(info) => {
                    info.current += 1;
                    if info.current >= info.total_count { break; }
                }
            }
        }

        // if we defined a non-local symbol, add it after we finish assembling that line (locals in this line should refer to past parent)
        if let Some((symbol, Locality::Nonlocal)) = args.label_def.take() { // we can take it since we're about to blow it up on next pass anyway
            args.last_nonlocal_label = Some(symbol);
        }
    }

    // link each symbol to internal symbols (minimizes file size and allows us to eliminate resolved internals)
    for (_, (expr, _)) in args.file.symbols.iter() {
        if let Err(EvalError::Illegal(reason)) = expr.eval(&args.file.symbols) {
            return Err(AsmError { kind: AsmErrorKind::ExprIllegalError(reason), line_num: args.line_num, pos: None, inner_err: None });
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
        if !is_reserved_symbol_name(to) { return Err(LinkError::EntryPointTargetWasReservedSymbol); }

        match objs[0].1.rename_symbol(from, to) {
            Ok(()) => (),
            Err(e) => match e {
                RenameError::TargetAlreadyExisted => return Err(LinkError::EntryPointTargetAlreadyExisted),
                RenameError::SourceWasAlreadyEvaluated => unreachable!(), // we know it's an extern, so this can't happen
                RenameError::SourceDidNotExist => unreachable!(), // we know it's an extern, so this can't happen
            }
        }
    }

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

    let mut binary_set = BinarySet::new(); // consolidated set of all included binary constants
    let mut obj_to_binary_set_locations: HashMap<usize, Vec<usize>> = Default::default(); // maps included obj to its literal index map in binary_set.

    let mut included: HashMap<usize, SegmentBases> = Default::default(); // maps included files to their segment bases in the result
    let mut include_queue: VecDeque<usize> = Default::default();
    include_queue.push_back(0); // we always start with the start file

    while let Some(obj_index) = include_queue.pop_front() {
        let (obj_name, obj) = &mut objs[obj_index];

        // account for alignment requirements
        align_seg(&mut text, &mut text_align, obj.text_align);
        align_seg(&mut rodata, &mut rodata_align, obj.rodata_align);
        align_seg(&mut data, &mut data_align, obj.data_align);
        align_seg(&mut bss_len, &mut bss_align, obj.bss_align);

        // add it to the set of included files
        let bases = SegmentBases { text: text.len(), rodata: rodata.len(), data: data.len(), bss: bss_len };
        assert!(included.insert(obj_index, bases).is_none());

        // offset holes to be relative to the start of their total segment (not relative to resulting file)
        for hole in obj.text_holes.iter_mut() { hole.address += bases.text; }
        for hole in obj.rodata_holes.iter_mut() { hole.address += bases.rodata; }
        for hole in obj.data_holes.iter_mut() { hole.address += bases.data; }

        // append segments
        text.extend_from_slice(&obj.text);
        rodata.extend_from_slice(&obj.rodata);
        data.extend_from_slice(&obj.data);
        bss_len += obj.bss_len;

        // for any external symbol we have, schedule the (single) associated object file defining it for inclusion
        for (req, _) in obj.extern_symbols.iter() {
            match global_to_obj.get(req) {
                None => return Err(LinkError::ExternSymbolNotDefined { ident: req.to_owned(), required_by: obj_name.to_owned() }),
                Some(other_index) => if !included.contains_key(other_index) && !include_queue.contains(other_index) {
                    include_queue.push_back(*other_index); // only schedule for inclusion if not already included and not already scheduled
                }
            }
        }

        // merge binary constants and keep track of their new slice indices
        let mut binary_set_locations: Vec<usize> = Vec::with_capacity(obj.binary_set.len());
        for bin in obj.binary_set.iter() {
            let loc = binary_set.add(bin);
            binary_set_locations.push(loc);
        }
        assert!(obj_to_binary_set_locations.insert(obj_index, binary_set_locations).is_none());
    }

    // after merging, but before alignment, we need to allocate all the provisioned binary constants
    let (backing_bin, slice_bin) = binary_set.decompose();
    let mut rodata_backing_bin_offsets: Vec<usize> = Vec::with_capacity(backing_bin.len());
    for backing in backing_bin.iter() {
        rodata_backing_bin_offsets.push(rodata.len()); // keep track of insertion point
        rodata.extend_from_slice(backing); // insert into rodata segment
    }
    // and now we can go ahead and resolve all the missing binary constant symbols with relative addresses from rodata origin
    for entry in obj_to_binary_set_locations {
        for (i, loc) in entry.1.into_iter().enumerate() {
            let slice = slice_bin[loc];
            let expr = Expr::from((OP::Add, ExprData::Ident(get_seg_origin_str(AsmSegment::Rodata).into()), (rodata_backing_bin_offsets[slice.src] + slice.start) as i64));
            objs[entry.0].1.symbols.define(format!("{}{:x}", BINARY_LITERAL_SYMBOL_PREFIX, i), expr, 0).unwrap();
        }
    }

    // account for segment alignments (we do this as if we already merged them, but don't yet due to overcomplicating hole patching
    { let s = text.len();                             pad(&mut text, align_off(s, rodata_align)); }
    { let s = text.len() + rodata.len();              pad(&mut rodata, align_off(s, data_align)); }
    { let s = text.len() + rodata.len() + data.len(); pad(&mut text, align_off(s, rodata_align)); }

    // now that we're done merging files, we need to define segment offsets in the result
    for (&obj_index, bases) in included.iter() {
        let (obj_name, obj) = &mut objs[obj_index];

        // define segment origins
        obj.symbols.define(get_seg_origin_str(AsmSegment::Text).into(), Value::Pointer(0).into(), 0).unwrap();
        obj.symbols.define(get_seg_origin_str(AsmSegment::Rodata).into(), Value::Pointer(text.len() as u64).into(), 0).unwrap();
        obj.symbols.define(get_seg_origin_str(AsmSegment::Data).into(), Value::Pointer((text.len() + rodata.len()) as u64).into(), 0).unwrap();
        obj.symbols.define(get_seg_origin_str(AsmSegment::Bss).into(), Value::Pointer((text.len() + rodata.len() + data.len()) as u64).into(), 0).unwrap();

        // define segment offsets
        obj.symbols.define(get_seg_offset_str(AsmSegment::Text).into(), Value::Pointer(bases.text as u64).into(), 0).unwrap();
        obj.symbols.define(get_seg_offset_str(AsmSegment::Text).into(), Value::Pointer((text.len() + bases.rodata) as u64).into(), 0).unwrap();
        obj.symbols.define(get_seg_offset_str(AsmSegment::Text).into(), Value::Pointer((text.len() + rodata.len() + bases.data) as u64).into(), 0).unwrap();
        obj.symbols.define(get_seg_offset_str(AsmSegment::Text).into(), Value::Pointer((text.len() + rodata.len() + data.len() + bases.bss) as u64).into(), 0).unwrap();

        // we must evaluate all global symbols at this point - next step copies them into other files; if we don't eval now we might use arbitrary symbol tables later
        for (global, _) in obj.global_symbols.iter() {
            let (expr, _) = obj.symbols.get(global).unwrap();
            match expr.eval(&obj.symbols) {
                Ok(_) => (), // success is the only legal option
                Err(e) => match e {
                    EvalError::Illegal(reason) => return Err(LinkError::GlobalExprIllegal { src: obj_name.clone(), ident: global.into(), reason }),
                    EvalError::UndefinedSymbol(_) => panic!(), // this should be impossible due to assembler guarantees
                }
            }
        }
    }

    // now that globals have been evaluated locally, we can copy them to wherever they're needed
    for (&obj_index, _) in included.iter() {
        let their_externs = mem::take(&mut objs[obj_index].1.extern_symbols); // we need to mutate and copy from objs at same time, so steal this
        for (external, _) in their_externs {
            let (val, _) = objs[*global_to_obj.get(&external).unwrap()].1.symbols.get(&external).unwrap().clone();
            objs[obj_index].1.symbols.define(external, val, 0).unwrap();
        }
    }

    // patch everything from every included file
    for (&obj_index, _) in included.iter() {
        let (obj_name, obj) = &objs[obj_index];
        elim_all_holes(obj_name, &mut text, &obj.text_holes, &obj.symbols)?;
        elim_all_holes(obj_name, &mut rodata, &obj.rodata_holes, &obj.symbols)?;
        elim_all_holes(obj_name, &mut data, &obj.data_holes, &obj.symbols)?;
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