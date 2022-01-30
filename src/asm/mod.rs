//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, VecDeque};
use std::io::{self, Read, Write, BufRead};
use std::{fmt, mem, iter};
use std::cmp::Ordering;
use std::borrow::Cow;
use num_traits::FromPrimitive;

use binary_set::BinarySet;
use expr::*;
use constants::*;
use asm_args::*;
use caseless::Caseless;

use crate::common::serialization::*;
use crate::common::f80::F80;
use crate::common::{OPCode, Executable, Syscall};
use crate::common::util::Punctuated;

macro_rules! slice_slice {
    ($t:ty: $([$($v:ident),*$(,)?]),*$(,)?) => {
        &[
            $(&[$(<$t>::$v),*] as &[$t]),*
        ] as &[&[$t]]
    }
}
macro_rules! display_from_name {
    ($t:ty, $($tr:path),*) => {
        $(impl $tr for $t {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.get_name())
            }
        })*
    };
    ($t:ty) => {
        display_from_name! { $t, fmt::Display, fmt::Debug }
    }
}

mod binary_set;
pub mod expr;
mod caseless;
mod constants;
mod asm_args;

/// The types of errors associated with failed address parsing,
/// but for which we know the argument was intended to be an address.
#[derive(Debug)]
pub(crate) enum BadAddress {
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
    TypeUnsupported(ValueType),
    InteriorNotSingleExpr,
    PtrSpecWithoutSize,
    SizeNotRecognized,
    IllegalExpr(IllegalReason),
    BadBase,
}
impl fmt::Display for BadAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BadAddress::Unterminated => write!(f, "unterminated address"),
            BadAddress::SizeMissingPtr => write!(f, "pointed size specifier missing 'ptr'. e.g. dword ptr [...]"),
            BadAddress::RegMultNotCriticalExpr(e) => write!(f, "register multiplier was not a critical expression: {}", e),
            BadAddress::RegIllegalOp => write!(f, "register was connected by an operation other than +/-"),
            BadAddress::InvalidRegMults => write!(f, "invalid register multipliers. can have at most 2 registers, with one having 1x and the other having 1,2,4,8x"),
            BadAddress::ConflictingSizes => write!(f, "address expression had conflicting sizes"),
            BadAddress::SizeUnsupported => write!(f, "address expression had unsupported size. must be 16, 32, or 64 bits"),
            BadAddress::TypeUnsupported(t) => write!(f, "address expression had unsupported type: {}. must be integral", t),
            BadAddress::InteriorNotSingleExpr => write!(f, "address interior was not a (single) expression"),
            BadAddress::PtrSpecWithoutSize => write!(f, "'ptr' spec encountered without a size"),
            BadAddress::SizeNotRecognized => write!(f, "pointer size not recognized"),
            BadAddress::IllegalExpr(r) => write!(f, "address expression was illegal: {}", r),
            BadAddress::BadBase => write!(f, "failed to parse address expression"),
        }
    }
}

/// The kinds of errors that can occur during assembly.
/// These are meant to be specific enough to have customized, detailed error messages.
#[derive(Debug)]
pub(crate) enum AsmErrorKind {
    /// A read error occurred, which cause assembly to halt prematurely.
    ReadError(io::Error),

    /// Incorrect number of arguments supplied. Expected this many.
    ArgsExpectedCount(&'static [usize]),
    ArgsExpectedCountAtLeast(usize),
    ExtraContentAfterArgs,

    /// If index is `None` it implies there is only one argument.
    ValueInvalidType { index: Option<usize>, got: ValueType, expected: &'static [ValueType] },
    ArgumentInvalidType { index: Option<usize>, got: ArgumentType, expected: &'static [ArgumentType] },
    ArgumentsInvalidTypes { got: Vec<ArgumentType>, expected: &'static [&'static [ArgumentType]] },
    ArgumentInvalidSize { index: Option<usize>, got: Size, expected: Vec<Size> },
    ArgumentsInvalidSizes { got: Vec<Size>, expected: &'static [&'static [Size]] },
    SizeSpecNotAllowed { index: Option<usize> },

    /// Failed to evaluate a critical expression for the given reason.
    FailedCriticalExpression(EvalError),
    AssertFailure,

    InvalidPrefixForInstruction,
    PrefixWithoutInstruction,

    SegmentAlreadyCompleted,
    LabelOnSegmentLine,
    UseOfTildeNot,
    NumericLiteralWithZeroPrefix,

    ExpectedString,
    IncompleteString,
    IncompleteEscape,
    InvalidEscape,

    ExpectedExpr,
    UnclosedParen,
    ParenInteriorNotExpr,
    ExpectedCommaBeforeToken,
    UnrecognizedMacroInvocation,
    IllFormedNumericLiteral,
    
    ExpectedAddress,
    BadAddress(BadAddress),

    SymbolAlreadyDefined,
    LocalSymbolBeforeNonlocal,
    InvalidSymbolName,
    ReservedSymbolName,

    CharacterLiteralNotUnicode,
    CharacterLiteralNotSingleChar,

    LabelOutsideOfSegment,
    AddressOutsideOfSegment,
    
    TimesIterOutisideOfTimes,
    TimesMissingCount,
    TimesCountWasNegative,
    TimesCountTooLarge,
    TimesUsedOnEmptyLine,

    IfMissingExpr,
    IfUsedOnEmptyLine,

    UnrecognizedInstruction,
    SuggestInstruction { from: Caseless<'static>, to: &'static [Caseless<'static>] },

    WriteOutsideOfSegment,
    WriteInBssSegment,
    InstructionOutsideOfTextSegment,

    IllegalPatch(IllegalPatchReason),
    ExprIllegalError(IllegalReason),

    UnsupportedOperandSize { got: Size, expected: &'static [Size] },
    OperandsHadDifferentSizes(Size, Size),
    CouldNotDeduceOperandSize,

    FPUBinaryOpNeitherST0,
    FPUBinaryOpPop2SrcNotST0,

    EQUWithoutLabel,

    AlignValueNegative(rug::Integer),
    AlignValueExceedsMaxAlign(rug::Integer),
    AlignValueNotPowerOf2(u64),
    AlignOutsideOfSegment,

    ReserveValueNegative(rug::Integer),
    ReserveValueExceedsMaxReserve(rug::Integer),
    ReserveOutsideOfBss,

    IdentifierIsGlobalAndExtern,
    RedundantGlobalOrExternDecl { prev_line_num: usize },
    GlobalSymbolWasNotDefined(String),
    UnknownSymbol(String),

    StringDeclareNotByteSize,

    VPUFailedToParseMaskArg,
    VPUMaskUnclosedBracket,
    VPUOpmaskWasK0,
    VPUZeroingWithoutOpmask,
    VPUMaskUnrecognizedMode,
    VPUMaskOnNondestArg,
    VPUMaskOnInstructionWithoutElemSize,
    VPUMaskOnNonVecInstruction,
}
impl From<BadAddress> for AsmErrorKind {
    fn from(reason: BadAddress) -> Self {
        AsmErrorKind::BadAddress(reason)
    }
}

/// The cause of a failure from [`assemble`].
/// 
/// This includes the line number and column of the error, and the inner error, if any.
/// However, to future-proof the assembler, the enum representing the actual error is private.
/// 
/// This type implements `Display` to get a user-level error message.
/// These error messages try to be as clear as possible and give hints about correct usage.
#[derive(Debug)]
pub struct AsmError {
    /// The type of error that was encountered.
    pub(crate) kind: AsmErrorKind,
    /// Line number of the error
    pub line_num: usize,
    /// Byte index of the error in the line (if relevant and available)
    pub pos: Option<usize>,
    /// Error which caused this error (if relevant)
    pub inner_err: Option<Box<AsmError>>,
}
impl fmt::Display for AsmError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.pos {
            Some(pos) => write!(f, "line {}:{} - ", self.line_num, pos),
            None => write!(f, "line {} - ", self.line_num),
        }?;
        match &self.kind {
            AsmErrorKind::ReadError(_) => write!(f, "io read error while assembling"),

            AsmErrorKind::ArgsExpectedCount(counts) => write!(f, "expected {} arguments", Punctuated::or(counts)),
            AsmErrorKind::ArgsExpectedCountAtLeast(min) => write!(f, "expected at least {} arguments", min),
            AsmErrorKind::ExtraContentAfterArgs => write!(f, "extra content after argument list (maybe a missing comma or semicolon?)"),

            AsmErrorKind::ValueInvalidType { index, got, expected } => match index {
                Some(index) => write!(f, "value {} invalid type {} - expected {}", index + 1, got, Punctuated::or(expected)),
                None => write!(f, "value invalid type {} - expected {}", got, Punctuated::or(expected)),
            }
            AsmErrorKind::ArgumentInvalidType { index, got, expected } => match index {
                Some(index) => write!(f, "argument {} invalid type {} - expected {}", index + 1, got, Punctuated::or(expected)),
                None => write!(f, "argument invalid type {} - expected {}", got, Punctuated::or(expected)),
            }
            AsmErrorKind::ArgumentsInvalidTypes { got, expected } => {
                write!(f, "arguments {:?} invalid types - expected {:?}", got, Punctuated::or(expected))
            }
            AsmErrorKind::ArgumentInvalidSize { index, got, expected } => match index {
                Some(index) => write!(f, "argument {} invalid size {} - expected {}", index + 1, got, Punctuated::or(expected)),
                None => write!(f, "argument invalid size {} - expected {}", got, Punctuated::or(expected)),
            }
            AsmErrorKind::ArgumentsInvalidSizes { got, expected } => {
                write!(f, "arguments {:?} invalid sizes - expected {:?}", got, Punctuated::or(expected))
            }
            AsmErrorKind::SizeSpecNotAllowed { index } => match index {
                Some(index) => write!(f, "size specifier on argument {} not allowed", index + 1),
                None => write!(f, "size specifier not allowed"),
            }

            AsmErrorKind::FailedCriticalExpression(e) => write!(f, "failed to evaluate a critical expression:\n    {}", e),
            AsmErrorKind::AssertFailure => write!(f, "assertion failed"),

            AsmErrorKind::InvalidPrefixForInstruction => write!(f, "invalid prefix for this instruction"),
            AsmErrorKind::PrefixWithoutInstruction => write!(f, "prefix encountered without an instruction"),

            AsmErrorKind::SegmentAlreadyCompleted => write!(f, "attempt to start a segment which is already defined"),
            AsmErrorKind::LabelOnSegmentLine => write!(f, "label encountered on a segment instruction (ambiguous target)"),
            AsmErrorKind::UseOfTildeNot => write!(f, "use of '~' for bitwise not. use '!' instead"),
            AsmErrorKind::NumericLiteralWithZeroPrefix => write!(f, "encountered C-style octal prefix. use '0o' instead"),

            AsmErrorKind::ExpectedString => write!(f, "expected a string"),
            AsmErrorKind::IncompleteString => write!(f, "incomplete string literal"),
            AsmErrorKind::IncompleteEscape => write!(f, "incomplete escape sequence"),
            AsmErrorKind::InvalidEscape => write!(f, "invalid escape sequence"),

            AsmErrorKind::ExpectedExpr => write!(f, "expected an expression term"),
            AsmErrorKind::UnclosedParen => write!(f, "unclosed parenthesis"),
            AsmErrorKind::ParenInteriorNotExpr => write!(f, "interior of parenthesized group was not a (single) expression"),
            AsmErrorKind::ExpectedCommaBeforeToken => write!(f, "expected comma before additional argument"),
            AsmErrorKind::UnrecognizedMacroInvocation => write!(f, "unrecognized macro invocation"),
            AsmErrorKind::IllFormedNumericLiteral => write!(f, "ill-formed numeric literal"),
            
            AsmErrorKind::ExpectedAddress => write!(f, "expected address"),
            AsmErrorKind::BadAddress(b) => write!(f, "bad address: {}", b),

            AsmErrorKind::SymbolAlreadyDefined => write!(f, "symbol was already defined"),
            AsmErrorKind::LocalSymbolBeforeNonlocal => write!(f, "local symbol with no prior global symbol"),
            AsmErrorKind::InvalidSymbolName => write!(f, "invalid symbol name"),
            AsmErrorKind::ReservedSymbolName => write!(f, "reserved symbol name"),

            AsmErrorKind::CharacterLiteralNotUnicode => write!(f, "character literal was not unicode"),
            AsmErrorKind::CharacterLiteralNotSingleChar => write!(f, "character literal was not a single character"),

            AsmErrorKind::LabelOutsideOfSegment => write!(f, "label outside of segment"),
            AsmErrorKind::AddressOutsideOfSegment => write!(f, "address macro outside of segment"),

            AsmErrorKind::TimesIterOutisideOfTimes => write!(f, "times iter macro outside of times directive"),
            AsmErrorKind::TimesMissingCount => write!(f, "times directive missing iteration count"),
            AsmErrorKind::TimesCountWasNegative => write!(f, "times directive count was negative"),
            AsmErrorKind::TimesCountTooLarge => write!(f, "times directive count was too large"),
            AsmErrorKind::TimesUsedOnEmptyLine => write!(f, "times directive used without an instruction to modify"),

            AsmErrorKind::IfMissingExpr => write!(f, "if directive missing condition"),
            AsmErrorKind::IfUsedOnEmptyLine => write!(f, "if directive used without an instruction to modify"),

            AsmErrorKind::UnrecognizedInstruction => write!(f, "unrecognized instruction"),
            AsmErrorKind::SuggestInstruction { from, to } => write!(f, "for clarity/consistency, {} is not a supported instruction. use {} instead.", from, Punctuated::or(to)),

            AsmErrorKind::WriteOutsideOfSegment => write!(f, "attempt to write data outside of any segment"),
            AsmErrorKind::WriteInBssSegment => write!(f, "attempt to write in bss segment (zeroed at runtime)"),
            AsmErrorKind::InstructionOutsideOfTextSegment => write!(f, "attempt to write instructions outside of text segment (not executable)"),

            AsmErrorKind::IllegalPatch(r) => write!(f, "invalid value encoding: {}", r),
            AsmErrorKind::ExprIllegalError(r) => write!(f, "expr illegal: {}", r),

            AsmErrorKind::UnsupportedOperandSize { got, expected } => write!(f, "operand size {} got not supported - expected {}", got, Punctuated::or(expected)),
            AsmErrorKind::OperandsHadDifferentSizes(s1, s2) => write!(f, "conflicting sizes: {} vs {}", s1, s2),
            AsmErrorKind::CouldNotDeduceOperandSize => write!(f, "failed to deduce operand sizes"),

            AsmErrorKind::FPUBinaryOpNeitherST0 => write!(f, "one of the arguments must be st0"),
            AsmErrorKind::FPUBinaryOpPop2SrcNotST0 => write!(f, "a popping fpu operation requires the source be st0"),

            AsmErrorKind::EQUWithoutLabel => write!(f, "the EQU directive requires a label, which becomes the symbol name"),

            AsmErrorKind::AlignValueNegative(val) => write!(f, "align value ({}) was negative", val),
            AsmErrorKind::AlignValueExceedsMaxAlign(val) => write!(f, "align value ({}) exceeded max align ({})", val, MAX_ALIGN),
            AsmErrorKind::AlignValueNotPowerOf2(val) => write!(f, "align value ({}) was not a power of 2", val),
            AsmErrorKind::AlignOutsideOfSegment => write!(f, "align outside of a segment"),

            AsmErrorKind::ReserveValueNegative(val) => write!(f, "reserve count ({}) was negative", val),
            AsmErrorKind::ReserveValueExceedsMaxReserve(val) => write!(f, "reserve count ({}) exceeded max reserve ({})", val, MAX_RESERVE),
            AsmErrorKind::ReserveOutsideOfBss => write!(f, "reserve can only be used inside the bss segment"),

            AsmErrorKind::IdentifierIsGlobalAndExtern => write!(f, "symbol marked as both global and extern"),
            AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num } => write!(f, "global/extern symbol was already declared on line {}", prev_line_num),
            AsmErrorKind::GlobalSymbolWasNotDefined(sym) => write!(f, "global symbol '{}' was never defined", sym),
            AsmErrorKind::UnknownSymbol(sym) => write!(f, "unknown symbol: '{}'", sym),

            AsmErrorKind::StringDeclareNotByteSize => write!(f, "attempt to write string with non-byte width (if utf16/32 encoding is desired, use the $utf16/32 macros"),

            AsmErrorKind::VPUFailedToParseMaskArg => write!(f, "failed to parse vpu opmask argument"),
            AsmErrorKind::VPUMaskUnclosedBracket => write!(f, "unclosed brace on vpu register opmask"),
            AsmErrorKind::VPUOpmaskWasK0 => write!(f, "used k0 as opmask (reserved encoding for no masking)"),
            AsmErrorKind::VPUZeroingWithoutOpmask => write!(f, "vpu opmask specified zeroing without a mask"),
            AsmErrorKind::VPUMaskUnrecognizedMode => write!(f, "vpu opmask unrecognized mode string"),
            AsmErrorKind::VPUMaskOnNondestArg => write!(f, "vpu opmasks are only allowed on the first operand"),
            AsmErrorKind::VPUMaskOnInstructionWithoutElemSize => write!(f, "vpu opmasks can only be used on instruction with fixed element size (e.g. vmovdqa won't work, but vmovdqa32 would)"),
            AsmErrorKind::VPUMaskOnNonVecInstruction => write!(f, "vpu opmasks can only be used on vector instructions"),
        }
    }
}

/// The cause of a failure from [`link`].
/// 
/// This contains information about any linking failure, including the source file(s) and line numbers, when necessary.
/// However, due to the variety of information needed for link errors and the need for future-proofing, this information is private.
/// 
/// This type implements `Display` to get a user level error message.
#[derive(Debug)]
pub struct LinkError {
    pub(crate) kind: LinkErrorKind,
}
impl From<LinkErrorKind> for LinkError {
    fn from(kind: LinkErrorKind) -> Self {
        Self { kind }
    }
}
impl fmt::Display for LinkError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.kind {
            LinkErrorKind::NothingToLink => write!(f, "nothing to link"),

            LinkErrorKind::EntryPointSourceNotExtern => write!(f, "start file did not declare the entry point source as extern"),
            LinkErrorKind::EntryPointTargetNotValidIdent => write!(f, "entry point target was not a valid identifier"),
            LinkErrorKind::EntryPointTargetWasReservedSymbol => write!(f, "entry point target was a reserved symbol"),
            LinkErrorKind::EntryPointTargetAlreadyExisted => write!(f, "start file defined a symbol with the same name as the entry point target"),
            LinkErrorKind::EntryPointTargetNotDefined => write!(f, "entry point target was not a global symbol from any input file"),

            LinkErrorKind::GlobalSymbolMultipleSources { ident, src1, src2 } => {
                write!(f, "global symbol '{}' was defined by both {}:{} and {}:{}", ident, src1.0, src1.1, src2.0, src2.1)
            }
            LinkErrorKind::ExternSymbolNotDefined { ident, required_by } => {
                write!(f, "extern symbol '{}' (required by {}) was not a global symbol from any input file", ident, required_by)
            }

            LinkErrorKind::EvalFailure { src, line_num, reason } => {
                write!(f, "failed to evaluate expr from {}:{} - {}", src, line_num, reason)
            }
            LinkErrorKind::PatchIllegal { src, line_num, reason } => {
                write!(f, "failed to patch missing value in {}:{} - {}", src, line_num, reason)
            }
        }
    }
}

#[derive(Debug)]
pub(crate) enum LinkErrorKind {
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

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ArgumentType {
    CPURegister,
    FPURegister,
    VPURegister,
    VPUMaskRegister,
    Address,
    Imm, Ident, // ident is subtype of imm
    Segment,
}
impl ArgumentType {
    fn get_name(&self) -> &'static str {
        match self {
            ArgumentType::CPURegister => "reg",
            ArgumentType::FPURegister => "st",
            ArgumentType::VPURegister => "vreg",
            ArgumentType::VPUMaskRegister => "kreg",
            ArgumentType::Address => "mem",
            ArgumentType::Imm => "imm",
            ArgumentType::Ident => "ident",
            ArgumentType::Segment => "seg",
        }
    }
}
display_from_name! { ArgumentType }

#[derive(Clone, Debug)]
enum Argument {
    CPURegister(CPURegisterInfo),
    FPURegister(FPURegisterInfo),
    VPUMaskRegister(VPUMaskRegisterInfo),
    VPURegister { reg: VPURegisterInfo, mask: Option<VPUMaskType> },
    Address { addr: Address, mask: Option<VPUMaskType> },
    Imm(Imm),
    Segment(AsmSegment),
}
impl Argument {
    fn get_type(&self) -> ArgumentType {
        match self {
            Argument::CPURegister(_) => ArgumentType::CPURegister,
            Argument::FPURegister(_) => ArgumentType::FPURegister,
            Argument::VPUMaskRegister(_) => ArgumentType::VPUMaskRegister,
            Argument::VPURegister { .. } => ArgumentType::VPURegister,
            Argument::Address { .. } => ArgumentType::Address,
            Argument::Imm(_) => ArgumentType::Imm,
            Argument::Segment(_) => ArgumentType::Segment,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Size {
    Byte,
    Word,
    Dword,
    Qword,

    Xword,
    Yword,
    Zword,

    Tword,
}
display_from_name! { Size }
impl Size {
    fn get_name(&self) -> &'static str {
        match self {
            Size::Byte => "byte",
            Size::Word => "word",
            Size::Dword => "dword",
            Size::Qword => "qword",

            Size::Xword => "xword",
            Size::Yword => "yword",
            Size::Zword => "zword",

            Size::Tword => "tword",
        }
    }

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

#[derive(Clone, Copy, PartialEq, Eq, FromPrimitive)]
#[repr(u8)]
pub(crate) enum HoleType {
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
impl HoleType {
    fn get_name(&self) -> &'static str {
        match self {
            HoleType::Pointer => "ptr",
            HoleType::Integer => "int",
            HoleType::Float => "float",
            HoleType::Any => "any",
        }
    }
}
display_from_name! { HoleType }

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

/// An assembled CSX64 object file.
/// 
/// These are produced from [`assemble`] and can be passed to [`link`] to generate an executable.
/// 
/// This type implements [`BinaryWrite`] and [`BinaryRead`] for serializing to/from a compact cross-platform binary representation.
/// Due to a quirk of the symbol table for expression collapsing, this type is not currently `Sync`, so it cannot be shared between threads.
/// However, you could convert it into a `Vec<u8>` via `BinaryWrite` and share that representation among multiple threads.
/// This is currently how [`stdlib`] stores its global object files.
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
pub(crate) enum IllegalPatchReason {
    IllegalExpr(IllegalReason),
    HoleContentInvalidType(HoleType, ValueType),
    WriteAsUnsupportedSize(ValueType, Size),
    TruncatedSignificantBits(ValueType, Size),
}
impl fmt::Display for IllegalPatchReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IllegalPatchReason::IllegalExpr(r) => write!(f, "illegal expression: {}", r),
            IllegalPatchReason::HoleContentInvalidType(t1, t2) => match t1 {
                HoleType::Any => write!(f, "type {} is not encodable", t2),
                _ => write!(f, "invalid type: expected {} got {}", t1, t2),
            }
            IllegalPatchReason::WriteAsUnsupportedSize(t, s) => write!(f, "attempt to encode {} as unsupported size ({})", t, s),
            IllegalPatchReason::TruncatedSignificantBits(t, s) => write!(f, "encoding {} value as size {} truncated significant bits", t, s),
        }
    }
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
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type, val.get_type())), line_num: hole.line_num });
            }
            let mut buf = [0; 4];
            ch.encode_utf8(&mut buf);
            let utf8 = u32::from_le_bytes(buf);
            match hole.size {
                Size::Byte => {
                    if utf8 > u8::MAX as u32 { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(utf8 as u8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if utf8 > u16::MAX as u32 { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(utf8 as u16).to_le_bytes(), hole.address)
                }
                Size::Dword => segment_write_bin(seg, &(utf8 as u32).to_le_bytes(), hole.address),
                Size::Qword => segment_write_bin(seg, &(utf8 as u64).to_le_bytes(), hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteAsUnsupportedSize(val.get_type(), x)), line_num: hole.line_num }),
            }
        }
        Value::Integer(v) => {
            if hole.allowed_type != HoleType::Integer && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type, val.get_type())), line_num: hole.line_num });
            }
            match hole.size {
                Size::Byte => match v.to_i8().map(|v| v as u8).or(v.to_u8()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                Size::Word => match v.to_i16().map(|v| v as u16).or(v.to_u16()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                Size::Dword => match v.to_i32().map(|v| v as u32).or(v.to_u32()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                Size::Qword => match v.to_i64().map(|v| v as u64).or(v.to_u64()) {
                    None => return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }),
                    Some(v) => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                }
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteAsUnsupportedSize(val.get_type(), x)), line_num: hole.line_num }),
            }
        }
        Value::Pointer(v) => {
            if hole.allowed_type != HoleType::Pointer && hole.allowed_type != HoleType::Integer && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type, val.get_type())), line_num: hole.line_num });
            }
            match hole.size {
                Size::Byte => {
                    if *v as u8 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as u8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if *v as u16 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as u16).to_le_bytes(), hole.address)
                }
                Size::Dword => {
                    if *v as u32 as u64 != *v { return Err(PatchError{ kind: PatchErrorKind::Illegal(IllegalPatchReason::TruncatedSignificantBits(val.get_type(), hole.size)), line_num: hole.line_num }); }
                    segment_write_bin(seg, &(*v as u32).to_le_bytes(), hole.address)
                }
                Size::Qword => segment_write_bin(seg, &v.to_le_bytes(), hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteAsUnsupportedSize(val.get_type(), x)), line_num: hole.line_num }),
            }
        }
        Value::Float(v) => {
            if hole.allowed_type != HoleType::Float && hole.allowed_type != HoleType::Any {
                return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type, val.get_type())), line_num: hole.line_num });
            }
            match hole.size {
                Size::Dword => segment_write_bin(seg, &v.to_f32().to_le_bytes(), hole.address),
                Size::Qword => segment_write_bin(seg, &v.to_f64().to_le_bytes(), hole.address),
                Size::Tword => segment_write_bin(seg, &F80::from(v).0, hole.address),
                x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::WriteAsUnsupportedSize(val.get_type(), x)), line_num: hole.line_num }),
            }
        }
        x => return Err(PatchError { kind: PatchErrorKind::Illegal(IllegalPatchReason::HoleContentInvalidType(hole.allowed_type, x.get_type())), line_num: hole.line_num }),
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
                PatchErrorKind::NotPatched(reason) => return Err(LinkErrorKind::EvalFailure { src: src(hole.src), line_num: e.line_num, reason }.into()),
                PatchErrorKind::Illegal(reason) => return Err(LinkErrorKind::PatchIllegal { src: src(hole.src), line_num: e.line_num, reason }.into()),
            }
        }
    }
    Ok(())
}

fn process_global_extern(arguments: Vec<Argument>, add_to: &mut HashMap<String, usize>, check_in: &HashMap<String, usize>, line_num: usize) -> Result<(), AsmError> {
    if arguments.is_empty() { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCountAtLeast(1), line_num, pos: None, inner_err: None }); }
    for (i, arg) in arguments.into_iter().enumerate() {
        match arg {
            Argument::Imm(v) => { // supertype of desired type: ident
                if v.size.is_some() { return Err(AsmError { kind: AsmErrorKind::SizeSpecNotAllowed { index: Some(i) }, line_num, pos: None, inner_err: None }); }
                match v.expr.into_ident() {
                    Some(ident) => {
                        debug_assert!(is_valid_symbol_name(&ident) && !is_reserved_symbol_name(&ident));
                        if check_in.contains_key(&ident) { return Err(AsmError { kind: AsmErrorKind::IdentifierIsGlobalAndExtern, line_num, pos: None, inner_err: None }); }
                        if let Some(prev) = add_to.insert(ident, line_num) {
                            return Err(AsmError { kind: AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num: prev }, line_num, pos: None, inner_err: None });
                        }
                    }
                    None => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: Some(i), got: ArgumentType::Imm, expected: &[ArgumentType::Ident] }, line_num, pos: None, inner_err: None })
                }
            }
            x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: Some(i), got: x.get_type(), expected: &[ArgumentType::Ident] }, line_num, pos: None, inner_err: None }),
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
#[test]
fn test_zero_pow2() {
    assert!(!0u64.is_power_of_two());
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
    seg.align_to(tail_align);
    *seg_align = tail_align.max(*seg_align);
}
#[test]
fn test_align_seg() {
    let mut seg: Vec<u8> = vec![];
    let mut align = 1;

    align_seg(&mut seg, &mut align, 8);
    assert_eq!(seg.len(), 0);
    assert_eq!(align, 8);

    seg.push(0);
    assert_eq!(seg.len(), 1);
    align_seg(&mut seg, &mut align, 4);
    assert_eq!(seg.len(), 4);
    assert_eq!(align, 8);
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
/// 
/// This type implements `Default`, which will give the set of default predefines.
/// These includes things such as the system call codes.
/// You can add more symbols on top of this with [`Predefines::append`].
/// 
/// Alternatively, you can use `From<SymbolTable<()>>` to construct a predefines table which has only your symbols.
/// Note that this will not have the default symbols.
pub struct Predefines(SymbolTable<usize>);
impl From<SymbolTable<()>> for Predefines {
    /// Constructs a new set of predefines from a symbol table.
    /// 
    /// Note that this will not include any of the default symbols.
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

/// Attempts to assemble the `asm` source file into an [`ObjectFile`].
/// 
/// It is not required that `asm` be an actual file.
/// Notably, `&mut &[u8]` can be used, which is useful for assembling an asm file stored in a string: `&mut some_string.as_bytes()`.
/// 
/// `asm_name` is the effective name of the source file (the assembly program can access its own file name).
/// It is recommended that `asm_name` be meaningful, as it might be used by the `asm` program to construct error messages, but this is not required.
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
                    if let Instruction::Suggest { from, to } = instruction { // handle this first in case there's an invalid prefix on a suggestion
                        return Err(AsmError { kind: AsmErrorKind::SuggestInstruction { from, to }, line_num: args.line_num, pos: None, inner_err: None });
                    }
                    match prefix { // then we proceed into the handlers
                        Some((Prefix::REP, prefix_pos)) => match instruction {
                            Instruction::MOVS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((1 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::LODS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((6 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::STOS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((8 << 2) | size.basic_sizecode().unwrap()))?,
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        Some((Prefix::REPZ, prefix_pos)) => match instruction {
                            Instruction::CMPS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((3 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::SCAS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((10 << 2) | size.basic_sizecode().unwrap()))?,
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        Some((Prefix::REPNZ, prefix_pos)) => match instruction {
                            Instruction::CMPS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((4 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::SCAS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((11 << 2) | size.basic_sizecode().unwrap()))?,
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        Some((Prefix::LOCK, prefix_pos)) => match instruction {
                            _ => return Err(AsmError { kind: AsmErrorKind::InvalidPrefixForInstruction, line_num: args.line_num, pos: Some(prefix_pos), inner_err: None }),
                        }
                        None => match instruction {
                            Instruction::MOVS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((0 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::CMPS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((2 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::LODS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((5 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::STOS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((7 << 2) | size.basic_sizecode().unwrap()))?,
                            Instruction::SCAS(size) => args.process_no_arg_op(arguments, Some(OPCode::STRING as u8), Some((9 << 2) | size.basic_sizecode().unwrap()))?,

                            Instruction::EQU => match &args.label_def {
                                None => return Err(AsmError { kind: AsmErrorKind::EQUWithoutLabel, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }),
                                Some((name, _)) => {
                                    if arguments.len() != 1 {
                                        return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None });
                                    }
                                    let val = match arguments.into_iter().next().unwrap() {
                                        Argument::Imm(imm) => {
                                            if let Some(_) = imm.size {
                                                return Err(AsmError { kind: AsmErrorKind::SizeSpecNotAllowed { index: None }, line_num: args.line_num, pos: None, inner_err: None });
                                            }
                                            imm.expr
                                        }
                                        x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: None, got: x.get_type(), expected: &[ArgumentType::Imm] }, line_num: args.line_num, pos: None, inner_err: None }),
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
                                    x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: None, got: x.get_type(), expected: &[ArgumentType::Segment] }, line_num: args.line_num, pos: None, inner_err: None }),
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
                                        if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::SizeSpecNotAllowed { index: None }, line_num: args.line_num, pos: None, inner_err: None }); }
                                        let val = match imm.expr.eval(&args.file.symbols) {
                                            Err(e) => return Err(AsmError { kind: AsmErrorKind::FailedCriticalExpression(e), line_num: args.line_num, pos: None, inner_err: None }),
                                            Ok(res) => match &*res {
                                                Value::Integer(v) => {
                                                    if v.cmp0() == Ordering::Less { return Err(AsmError { kind: AsmErrorKind::AlignValueNegative(v.clone()), line_num: args.line_num, pos: None, inner_err: None }); }
                                                    match v.to_u64() {
                                                        None => return Err(AsmError { kind: AsmErrorKind::AlignValueExceedsMaxAlign(v.clone()), line_num: args.line_num, pos: None, inner_err: None }),
                                                        Some(v) => v,
                                                    }
                                                }
                                                x => return Err(AsmError { kind: AsmErrorKind::ValueInvalidType { index: None, got: x.get_type(), expected: &[ValueType::Integer] }, line_num: args.line_num, pos: None, inner_err: None }),
                                            }
                                        };
                                        if val > MAX_ALIGN { return Err(AsmError { kind: AsmErrorKind::AlignValueExceedsMaxAlign(val.into()), line_num: args.line_num, pos: None, inner_err: None }); }
                                        if !val.is_power_of_two() { return Err(AsmError { kind: AsmErrorKind::AlignValueNotPowerOf2(val), line_num: args.line_num, pos: None, inner_err: None }); }
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
                                    x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: None, got: x.get_type(), expected: &[ArgumentType::Imm] }, line_num: args.line_num, pos: None, inner_err: None }),
                                }
                            }
                            Instruction::ASSERT => {
                                if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                let cond = match arguments.into_iter().next().unwrap() {
                                    Argument::Imm(imm) => {
                                        if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::SizeSpecNotAllowed { index: None }, line_num: args.line_num, pos: None, inner_err: None }); }
                                        match imm.expr.eval(&args.file.symbols) {
                                            Err(e) => return Err(AsmError { kind: AsmErrorKind::FailedCriticalExpression(e), line_num: args.line_num, pos: None, inner_err: None }),
                                            Ok(res) => match &*res {
                                                Value::Logical(v) => *v,
                                                v => return Err(AsmError { kind: AsmErrorKind::ValueInvalidType { index: None, got: v.get_type(), expected: &[ValueType::Logical] }, line_num: args.line_num, pos: None, inner_err: None }),
                                            }
                                        }
                                    }
                                    x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: None, got: x.get_type(), expected: &[ArgumentType::Imm] }, line_num: args.line_num, pos: None, inner_err: None }),
                                };
                                if !cond { return Err(AsmError { kind: AsmErrorKind::AssertFailure, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                            }
                            Instruction::DECLARE(size) => {
                                if arguments.len() < 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCountAtLeast(1), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                for (i, arg) in arguments.into_iter().enumerate() {
                                    match arg {
                                        Argument::Imm(imm) => {
                                            if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::SizeSpecNotAllowed { index: Some(i) }, line_num: args.line_num, pos: None, inner_err: None }); }
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
                                        x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: Some(i), got: x.get_type(), expected: &[ArgumentType::Imm] }, line_num: args.line_num, pos: None, inner_err: None }),
                                    }
                                }
                            }
                            Instruction::RESERVE(size) => {
                                if args.current_seg != Some(AsmSegment::Bss) { return Err(AsmError { kind: AsmErrorKind::ReserveOutsideOfBss, line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                if arguments.len() != 1 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1]), line_num: args.line_num, pos: Some(instruction_pos), inner_err: None }); }
                                match arguments.into_iter().next().unwrap() {
                                    Argument::Imm(imm) => {
                                        if imm.size.is_some() { return Err(AsmError { kind: AsmErrorKind::SizeSpecNotAllowed { index: None }, line_num: args.line_num, pos: None, inner_err: None }); }
                                        let count = match imm.expr.eval(&args.file.symbols) {
                                            Err(e) => return Err(AsmError { kind: AsmErrorKind::FailedCriticalExpression(e), line_num: args.line_num, pos: None, inner_err: None }),
                                            Ok(res) => match &*res {
                                                Value::Integer(v) => {
                                                    if v.cmp0() == Ordering::Less { return Err(AsmError { kind: AsmErrorKind::ReserveValueNegative(v.clone()), line_num: args.line_num, pos: None, inner_err: None }); }
                                                    match v.to_u64() {
                                                        None => return Err(AsmError { kind: AsmErrorKind::ReserveValueExceedsMaxReserve(v.clone()), line_num: args.line_num, pos: None, inner_err: None }),
                                                        Some(v) => v,
                                                    }
                                                }
                                                x => return Err(AsmError { kind: AsmErrorKind::ValueInvalidType { index: None, got: x.get_type(), expected: &[ValueType::Integer] }, line_num: args.line_num, pos: None, inner_err: None }),
                                            }
                                        };
                                        if count > MAX_RESERVE { return Err(AsmError { kind: AsmErrorKind::ReserveValueExceedsMaxReserve(count.into()), line_num: args.line_num, pos: None, inner_err: None }); }
                                        let bytes = count as usize * size.size();
                                        args.file.bss_len += bytes;
                                    }
                                    x => return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidType { index: None, got: x.get_type(), expected: &[ArgumentType::Imm] }, line_num: args.line_num, pos: None, inner_err: None }),
                                }
                            }
                            Instruction::LEA => {
                                if arguments.len() != 2 { return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[2]), line_num: args.line_num, pos: None, inner_err: None }); }
                                let mut arguments = arguments.into_iter();
                                let a = arguments.next().unwrap();
                                let b = arguments.next().unwrap();

                                let supported_types = slice_slice!(ArgumentType:
                                    [CPURegister, Address],
                                );

                                let (reg, addr) = match (a, b) {
                                    (Argument::CPURegister(reg), Argument::Address { addr, mask }) => {
                                        if mask.is_some() { return Err(AsmError { kind: AsmErrorKind::VPUMaskOnNonVecInstruction, line_num: args.line_num, pos: None, inner_err: None }); }
                                        if reg.size == Size::Byte { return Err(AsmError { kind: AsmErrorKind::ArgumentInvalidSize { index: Some(0), got: reg.size, expected: vec![Size::Word, Size::Dword, Size::Qword] }, line_num: args.line_num, pos: None, inner_err: None }); }
                                        (reg, addr)
                                    }
                                    (a, b) => return Err(AsmError { kind: AsmErrorKind::ArgumentsInvalidTypes { got: vec![a.get_type(), b.get_type()], expected: supported_types }, line_num: args.line_num, pos: None, inner_err: None }),
                                };
        
                                args.append_byte(OPCode::LEA as u8)?;
                                args.append_byte((reg.id << 4) | (reg.size.basic_sizecode().unwrap() << 2))?;
                                args.append_address(addr)?;
                            }
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
                                    args.process_unary_op(arguments, OPCode::CMPZ as u8, None, STANDARD_SIZES)?
                                }
                                else { args.process_binary_op(arguments, OPCode::CMP as u8, None, HoleType::Integer, STANDARD_SIZES, None, None)? }
                            }
                            Instruction::MUL => match arguments.len() {
                                1 => args.process_value_op(arguments, OPCode::MULDIV as u8, Some(0), HoleType::Integer, STANDARD_SIZES, None)?,
                                2 => args.process_binary_op(arguments, OPCode::MULDIV as u8, Some(1), HoleType::Integer, STANDARD_SIZES, None, None)?,
                                3 => args.process_ternary_op(arguments, OPCode::MULDIV as u8, Some(2), HoleType::Integer, STANDARD_SIZES, None, None)?,
                                _ => return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1, 2, 3]), line_num: args.line_num, pos: None, inner_err: None }),
                            }
                            Instruction::IMUL => match arguments.len() {
                                1 => args.process_value_op(arguments, OPCode::MULDIV as u8, Some(4), HoleType::Integer, STANDARD_SIZES, None)?,
                                2 => args.process_binary_op(arguments, OPCode::MULDIV as u8, Some(5), HoleType::Integer, STANDARD_SIZES, None, None)?,
                                3 => args.process_ternary_op(arguments, OPCode::MULDIV as u8, Some(6), HoleType::Integer, STANDARD_SIZES, None, None)?,
                                _ => return Err(AsmError { kind: AsmErrorKind::ArgsExpectedCount(&[1, 2, 3]), line_num: args.line_num, pos: None, inner_err: None }),
                            }
                            Instruction::MOVEXT { signed } => args.process_mov_ext_op(arguments, OPCode::MOVEXT as u8, None, signed)?,

                            Instruction::NoArg { op, ext_op } => args.process_no_arg_op(arguments, op, ext_op)?,
                            Instruction::Unary { op, ext_op, allowed_sizes } => args.process_unary_op(arguments, op, ext_op, allowed_sizes)?,
                            Instruction::Binary { op, ext_op, allowed_type, allowed_sizes, force_b_rm_size, force_b_imm_size } => args.process_binary_op(arguments, op, ext_op, allowed_type, allowed_sizes, force_b_rm_size, force_b_imm_size)?,
                            Instruction::BinaryLvalueUnord { op, ext_op, allowed_sizes } => args.process_binary_lvalue_unordered_op(arguments, op, ext_op, allowed_sizes)?,
                            Instruction::Ternary { op, ext_op, allowed_type, allowed_sizes, force_b_rm_size, force_b_imm_size } => args.process_ternary_op(arguments, op, ext_op, allowed_type, allowed_sizes, force_b_rm_size, force_b_imm_size)?,
                            Instruction::Value { op, ext_op, allowed_type, allowed_sizes, default_size } => args.process_value_op(arguments, op, ext_op, allowed_type, allowed_sizes, default_size)?,

                            Instruction::FPUBinary { op, ext_op, int, pop } => args.process_fpu_binary_op(arguments, op, ext_op, int, pop)?,
                            Instruction::FPUValue { op, ext_op, int } => args.process_fpu_value_op(arguments, op, ext_op, int)?,
                            
                            Instruction::VPUKMove { size } => args.process_kmov(arguments, size)?,
                            Instruction::VPUMove { elem_size, packed, aligned, cpu_transfer } => args.process_vpu_move(arguments, elem_size, packed, aligned, cpu_transfer)?,
                            Instruction::VPUBinary { op, ext_op, elem_size, packed } => args.process_vpu_binary_op(arguments, op, ext_op, elem_size, packed)?,

                            Instruction::Suggest { .. } => unreachable!(),
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
/// Attempts to link one or more (named) [`ObjectFile`]s into an [`Executable`].
/// 
/// This function combines several incomplete object files together into a final, complete version.
/// This starts with the first file, `objs[0]`, and branches out to includes any extern symbols, recursively.
/// Only files which are needed will be included in the final result.
/// 
/// The first object file, `objs[0]` is known as the "start file".
/// The start file's text segment (starting at the beginning) is the first thing to execute upon running the resulting executable.
/// For very basic programs this is fine, but using a higher-level framework might require setup prior to running the "main" logic.
/// Typically, this is denoted by a generic symbol such as "start" (hence, start file).
/// If `entry_point` is `Some((from, to))`, the linker will perform a renaming operation for identifiers in the start file (only).
/// 
/// If you wish to use the included C standard library functions, first call [`stdlib`] to get the object files, which includes its own start file at the front of the vec.
/// Then, you need only add your object files to the end (with a global named "main" somewhere), and pass `Some(("start", "main"))`.
pub fn link(mut objs: Vec<(String, ObjectFile)>, entry_point: Option<(&str, &str)>) -> Result<Executable, LinkError> {
    if objs.is_empty() { return Err(LinkErrorKind::NothingToLink.into()); }

    // if an entry point was specified, perform the replacement
    if let Some((from, to)) = entry_point {
        if !objs[0].1.extern_symbols.contains_key(from) { return Err(LinkErrorKind::EntryPointSourceNotExtern.into()); }

        if !is_valid_symbol_name(to) { return Err(LinkErrorKind::EntryPointTargetNotValidIdent.into()); }
        if is_reserved_symbol_name(to) { return Err(LinkErrorKind::EntryPointTargetWasReservedSymbol.into()); }

        match objs[0].1.rename_symbol(from, to) {
            Ok(()) => (),
            Err(e) => match e {
                RenameError::TargetAlreadyExisted => return Err(LinkErrorKind::EntryPointTargetAlreadyExisted.into()),
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
                return Err(LinkErrorKind::GlobalSymbolMultipleSources { ident: global.into(), src1: (objs[there_line].0.to_owned(), there_line), src2: (obj.0.to_owned(), here_line) }.into());
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
                    false => return Err(LinkErrorKind::ExternSymbolNotDefined { ident: req.to_owned(), required_by: obj_name.to_owned() }.into()),
                    true => return Err(LinkErrorKind::EntryPointTargetNotDefined.into()),
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
            ExprData::Uneval { op: OP::Intern, left, right } => {
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
                            a => return Err(LinkErrorKind::EvalFailure { src: src.into(), line_num, reason: IllegalReason::IncompatibleType(OP::Intern, a.get_type()).into() }.into()),
                        }
                    }
                }
                let res: ExprData = match left.take().expect("expr unary op node was missing the left branch").into_eval(symbols) {
                    Err(e) => return Err(LinkErrorKind::EvalFailure { src: src.into(), line_num, reason: e }.into()),
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
    { let s = text.len() + rodata.len() + data.len(); pad(&mut data, align_off(s, bss_align)); }
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
            return Err(LinkErrorKind::EvalFailure { src: objs[tag.src].0.to_owned(), line_num: tag.line_num, reason: e }.into());
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
                let obj = match assemble($name, &mut include_str!(concat!("../asm/stdlib/", $name)).as_bytes(), Default::default()) {
                    Ok(x) => x,
                    Err(e) => panic!("failed to assemble stdlib: {}\n{}", $name, e),
                };
                let mut bin = vec![];
                obj.bin_write(&mut bin).unwrap();
                ($name, bin)
            }};
            ([ $($name:literal),+$(,)? ]) => {
                vec![$(assemble_physical_file!($name)),+]
            }
        }
        assemble_physical_file!([
            "start.asm", "malloc.asm", "exit.asm", "ctype.asm", "arglist.asm", "string.asm", "stdio.asm",
        ])
    };
}
/// Gets a copy of the C-style standard library [`ObjectFile`]s for use in CSX64 asm programs.
/// 
/// Notably, this includes the start file which is required by [`link`] to use entry points.
/// The standard library includes tools such as `malloc`, `free`, `printf`, etc.
/// 
/// If you wish to link one or more object files to the standard library, call this function and append your object files to the end.
/// The whole sequence can then be handed over to the linker, which will ensure that only the files that were reference are included in the result.
pub fn stdlib() -> Vec<(String, ObjectFile)> {
    STDLIB.iter().map(|(name, bin)| (name.to_string(), ObjectFile::bin_read(&mut bin.as_slice()).unwrap())).collect()
}