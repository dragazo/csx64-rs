//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, HashSet};
use std::io::{self, Read, Write, BufRead};

pub mod binary_set;
pub mod expr;
pub mod caseless;
mod constants;
mod asm_args;

use binary_set::BinarySet;
use expr::{Expr, SymbolTable, TypeSet};
use constants::*;
use asm_args::*;

use crate::common::serialization::*;

/// Grabs the first whitespace-separated token and returns it, along with the index just after it.
/// If no token is present, returns empty string and the index of one past the end of the input string.
fn grab_whitespace_sep_token(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    let token_start = match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        None => raw_stop,
        Some(p) => raw_start + p,
    };
    let token_stop = match raw_line[token_start..raw_stop].find(|c: char| c.is_whitespace()) {
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
}

/// Trims all leading whitespace characters and returns the result and the index of the starting portion.
/// If the string is empty or whitespace, returns empty string and one past the end of the input string.
fn trim_start_with_pos(raw_line: &str, raw_start: usize, raw_stop: usize) -> (&str, usize) {
    match raw_line[raw_start..raw_stop].find(|c: char| !c.is_whitespace()) {
        Some(p) => (&raw_line[raw_start + p..raw_stop], raw_start + p),
        None => ("", raw_stop),
    }
}
#[test]
fn test_trim_start_with_pos() {
    assert_eq!(trim_start_with_pos("   \t hello world  ", 3, 18), ("hello world  ", 5));
    assert_eq!(trim_start_with_pos("    \t  ", 1, 7), ("", 7));
    assert_eq!(trim_start_with_pos("", 0, 0), ("", 0));
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsmErrorKind {
    ReadError,

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
    IncorrectArgCount,
    IllFormedExpr,

    IllFormedNumericLiteral,
    NumericLiteralWithZeroPrefix,
    
    LocalSymbolBeforeNonlocal,
    InvalidSymbolName,
    ReservedSymbolName,

    ExpectedBinaryValue,
    EmptyBinaryValue,

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
    
    FailedCriticalExpression,
    
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
}

#[derive(Debug)]
pub struct AsmError {
    pub kind: AsmErrorKind,
    pub pos: usize,
    pub line: String,
    pub line_num: usize,
}
#[derive(Debug)]
struct InternalAsmError {
    kind: AsmErrorKind,
    pos: usize,
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
    size: Size,                 // size of the address itself
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
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Size {
    Byte,
    Word,
    Dword,
    Qword,

    Xmmword,
    Ymmword,
    Zmmword,

    Tword,
}
impl Size {
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
            Size::Xmmword => Some(0),
            Size::Ymmword => Some(1),
            Size::Zmmword => Some(2),
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
            Size::Xmmword => 4,
            Size::Ymmword => 5,
            Size::Zmmword => 6,
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
            4 => Size::Xmmword,
            5 => Size::Ymmword,
            6 => Size::Zmmword,
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
    assert_eq!(Size::Xmmword.basic_sizecode(), None);
    assert_eq!(Size::Xmmword.vector_sizecode(), Some(0));
    assert_eq!(Size::Xmmword.vector_size(), Some(16));
    assert_eq!(Size::Ymmword.vector_sizecode(), Some(1));
    assert_eq!(Size::Ymmword.vector_size(), Some(32));
}

#[derive(Clone)]
struct Hole {
    address: u64,
    size: Size,
    line: usize,
    expr: Expr,
    allowed_types: TypeSet,
}
impl BinaryWrite for Hole {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.address.bin_write(f)?;
        self.size.bin_write(f)?;
        self.line.bin_write(f)?;
        self.expr.bin_write(f)?;
        self.allowed_types.bin_write(f)
    }
}
impl BinaryRead for Hole {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Hole> {
        let address = BinaryRead::bin_read(f)?;
        let size = BinaryRead::bin_read(f)?;
        let line = BinaryRead::bin_read(f)?;
        let expr = BinaryRead::bin_read(f)?;
        let allowed_types = BinaryRead::bin_read(f)?;
        Ok(Hole { address, size, line, expr, allowed_types })
    }
}

#[derive(Clone)]
pub struct ObjectFile {
    global_symbols: HashSet<String>,
    extern_symbols: HashSet<String>,

    symbols: SymbolTable,

    text_align: u32,
    rodata_align: u32,
    data_align: u32,
    bss_align: u32,

    text_holes: Vec<Hole>,
    rodata_holes: Vec<Hole>,
    data_holes: Vec<Hole>,

    text: Vec<u8>,
    rodata: Vec<u8>,
    data: Vec<u8>,
    bss_len: usize,

    binary_set: BinarySet,
}
impl BinaryWrite for ObjectFile {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
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

/// Attempts to assemble the `asm` source file into an `ObjectFile`.
/// It is not required that `asm` be an actual file - it can just be in memory.
/// `asm_name` is the effective name of the source file (the assembly program can access its own file name).
/// It is recommended that `asm_name` be meaningful, as it is might be used by the `asm` program to construct error messages, but this is not required.
pub fn assemble(asm_name: &str, asm: &mut dyn BufRead, predefines: SymbolTable) -> Result<ObjectFile, AsmError> {
    let mut args = AssembleArgs {
        file: ObjectFile {
            global_symbols: Default::default(),
            extern_symbols: Default::default(),

            symbols: predefines,

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

            binary_set: Default::default(),
        },

        current_seg: None,
        done_segs: Default::default(),

        line_num: 0,
        line_pos_in_seg: 0,

        last_nonlocal_label: None,
        
        times: None,
        
        label_def: None,
        instruction: None,
        arguments: Default::default(),
    };

    macro_rules! err {
        ($err:ident => $line:ident : $line_num:expr) => {
            Err(AsmError { kind: $err.kind, pos: $err.pos, line: $line, line_num: $line_num })
        }
    }

    let mut line = String::new();
    loop {
        line.clear();
        match asm.read_line(&mut line) {
            Err(_) => return Err(AsmError { kind: AsmErrorKind::ReadError, line, line_num: args.line_num, pos: 0 }),
            Ok(v) => if v == 0 { break; }
        }
        args.line_num += 1;
        let header_aft = match args.extract_header(&line) {
            Err(e) => return err!(e => line : args.line_num),
            Ok(v) => v,
        };
        debug_assert!(match line[header_aft..].chars().next() { Some(c) => c.is_whitespace() || c == COMMENT_CHAR, None => true });

        
    }

    Ok(args.file)
}