//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, HashSet};
use std::io::{self, Read, Write};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsmErrorKind {
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
    
    LocalSymbolBeforeNonlocal,
    InvalidSymbolName,

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
}

#[derive(Debug)]
pub struct AsmError {
    pub kind: AsmErrorKind,
    pub line_num: usize,
    pub line: String,
    pub pos: usize,
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


