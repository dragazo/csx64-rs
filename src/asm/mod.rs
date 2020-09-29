//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, HashSet};
use std::io::{self, Read, Write};

pub mod binary_set;
pub mod expr;
mod constants;
mod asm_args;

use binary_set::BinarySet;
use expr::{Expr, SymbolTable};
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

    FailedParseImm,
    FailedParseAddress,
    FailedParseCPURegister,
    FailedParseFPURegister,
    FailedParseVPURegister,

    FailedCriticalExpression,
}

#[derive(Debug)]
pub struct AsmError {
    pub kind: AsmErrorKind,
    pub line_num: usize,
    pub line: String,
    pub pos: usize,
}

#[derive(Clone)]
struct Imm {
    expr: Expr,
    sizecode: Option<Sizecode>, // size of the value
}

#[derive(Clone)]
struct Address {
    base: Expr,
    a: u8,
    b: u8,
    sizecode: Option<Sizecode>, // size of the pointed-to value (not the address itself)
}

#[derive(Clone)]
enum Argument {
    CPURegister(CPURegisterInfo),
    FPURegister(FPURegisterInfo),
    VPURegister(VPURegisterInfo),
    Address(Address),
    Imm(Imm),
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Sizecode(u8);
impl Sizecode {
    const fn size(self) -> u8 {
        1 << self.0
    }
}
impl BinaryWrite for Sizecode {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.0.bin_write(f)
    }
}
impl BinaryRead for Sizecode {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Sizecode> {
        Ok(Sizecode(u8::bin_read(f)?))
    }
}

#[derive(Clone)]
struct Hole {
    address: u64,
    sizecode: Sizecode,
    line: usize,
    expr: Expr,
}
impl BinaryWrite for Hole {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.address.bin_write(f)?;
        self.sizecode.bin_write(f)?;
        self.line.bin_write(f)?;
        self.expr.bin_write(f)
    }
}
impl BinaryRead for Hole {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Hole> {
        let address = u64::bin_read(f)?;
        let sizecode = Sizecode::bin_read(f)?;
        let line = usize::bin_read(f)?;
        let expr = Expr::bin_read(f)?;
        Ok(Hole { address, sizecode, line, expr })
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


