//! Everything pertaining to the creation of CSX64 shared object files, object files, and executables.

use std::collections::{HashMap, HashSet};
use std::io::{self, Read, Write, BufRead};

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
use crate::common::OPCode;
use crate::common::f80::F80;

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
    ReadError, // failure while reading the file
    BoundsError, // index failure (corrupted input)

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

    UnrecognizedSegment,
    SegmentAlreadyCompleted,
    ExtraContentAfterSegmentName,
    LabelOnSegmentLine,

    IncorrectArgCount(u8),
    ExpectedExpressionArg(u8),

    WriteOutsideOfSegment,
    WriteInBssSegment,
    InstructionOutsideOfTextSegment,

    HoleContentInvalidType(HoleType),
    TruncatedSignificantBits,
    WriteIntegerAsUnsupportedSize(Size),
    WriteFloatAsUnsupportedSize(Size),

    UnsupportedOperandSize,
    OperandsHadDifferentSizes,
    SizeSpecOnForcedSize,
    BinaryOpUnsupportedSrcDestTypes, // e.g. memory x memory
    CouldNotDeduceOperandSize,

    EQUWithoutLabel,
    EQUArgumentHadSizeSpec,
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
    line_num: usize,
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
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Size {
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
    /// Returns the size of this type in bytes.
    fn size(self) -> usize {
        match self {
            Size::Byte => 1,
            Size::Word => 2,
            Size::Dword => 4,
            Size::Qword => 8,
            Size::Xmmword => 16,
            Size::Ymmword => 32,
            Size::Zmmword => 64,
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HoleType {
    Signed,
    Unsigned,
    Pointer,
    Integral, // signed, unsigned, or pointer
    Floating,
}
impl BinaryWrite for HoleType {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            HoleType::Signed => 0u8,
            HoleType::Unsigned => 1u8,
            HoleType::Pointer => 2u8,
            HoleType::Integral => 3u8,
            HoleType::Floating => 4u8,
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

/// Writes a binary value to the given segment at the specified position.
/// If the value is out of bounds, fails with Err, otherwise always succeeds.
fn segment_write_bin(seg: &mut Vec<u8>, val: &[u8], pos: usize) -> Result<(), ()> {
    match seg.get_mut(pos..pos+val.len()) {
        None => Err(()),
        Some(dest) => {
            dest.copy_from_slice(val);
            Ok(())
        }
    }
}

#[derive(Debug)]
enum PatchError {
    Illegal(InternalAsmError),
    NotPatched(EvalError),
}

/// Attempts to patch the hole in the given segment.
/// On critical (bad/illegal) failure, returns Err.
/// Otherwise returns Ok(Err) if evaluation fails (this is not a bad error, as it might can be patched later).
/// Returns Ok(OK(())) to denote that everything succeeded and the hole was successfully patched.
fn patch_hole(seg: &mut Vec<u8>, symbols: &SymbolTable, hole: &Hole) -> Result<(), PatchError> {
    let val = match hole.expr.eval(symbols) {
        Err(e) => return Err(PatchError::NotPatched(e)),
        Ok(v) => v,
    };

    macro_rules! err {
        ($hole:ident => $kind:expr) => {
            Err(PatchError::Illegal(InternalAsmError { line_num: $hole.line_num, pos: 0, kind: $kind }))
        }
    }

    let write_res = match &*val {
        Value::Signed(v) => {
            if hole.allowed_type != HoleType::Signed && hole.allowed_type != HoleType::Integral {
                return err!(hole => AsmErrorKind::HoleContentInvalidType(hole.allowed_type)); 
            }
            match hole.size {
                Size::Byte => {
                    if *v as i8 as i64 != *v { return err!(hole => AsmErrorKind::TruncatedSignificantBits); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if *v as i16 as i64 != *v { return err!(hole => AsmErrorKind::TruncatedSignificantBits); }
                    segment_write_bin(seg, &(*v as i16).to_le_bytes(), hole.address)
                }
                Size::Dword => {
                    if *v as i32 as i64 != *v { return err!(hole => AsmErrorKind::TruncatedSignificantBits); }
                    segment_write_bin(seg, &(*v as i32).to_le_bytes(), hole.address)
                }
                Size::Qword => segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address),
                x => return err!(hole => AsmErrorKind::WriteIntegerAsUnsupportedSize(x)),
            }
        }
        Value::Unsigned(v) | Value::Pointer(v) => {
            if hole.allowed_type != HoleType::Unsigned && hole.allowed_type != HoleType::Integral {
                return err!(hole => AsmErrorKind::HoleContentInvalidType(hole.allowed_type)); 
            }
            match hole.size {
                Size::Byte => {
                    if *v as u8 as u64 != *v { return err!(hole => AsmErrorKind::TruncatedSignificantBits); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Word => {
                    if *v as u16 as u64 != *v { return err!(hole => AsmErrorKind::TruncatedSignificantBits); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Dword => {
                    if *v as u32 as u64 != *v { return err!(hole => AsmErrorKind::TruncatedSignificantBits); }
                    segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address)
                }
                Size::Qword => segment_write_bin(seg, &(*v as i8).to_le_bytes(), hole.address),
                x => return err!(hole => AsmErrorKind::WriteIntegerAsUnsupportedSize(x)),
            }
        }
        Value::Floating(v) => {
            if hole.allowed_type != HoleType::Floating {
                return err!(hole => AsmErrorKind::HoleContentInvalidType(hole.allowed_type)); 
            }
            match hole.size {
                Size::Dword => segment_write_bin(seg, &v.to_f32().to_le_bytes(), hole.address),
                Size::Qword => segment_write_bin(seg, &v.to_f64().to_le_bytes(), hole.address),
                Size::Tword => segment_write_bin(seg, &F80::from(v).0, hole.address),
                x => return err!(hole => AsmErrorKind::WriteIntegerAsUnsupportedSize(x)),
            }
        }
        _ => return err!(hole => AsmErrorKind::HoleContentInvalidType(hole.allowed_type)),
    };
    match write_res {
        Err(_) => Err(PatchError::Illegal(InternalAsmError { line_num: hole.line_num, pos: 0, kind: AsmErrorKind::BoundsError })),
        Ok(_) => Ok(()),
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

        label_def: None,
        last_nonlocal_label: None,
        
        times: None,
    };

    macro_rules! err {
        ($err:ident => $line:ident : $line_num:expr) => {
            Err(AsmError { kind: $err.kind, pos: $err.pos, line: $line, line_num: $line_num })
        };
        ($pos:expr, $kind:expr => $line:ident : $line_num:expr) => {
            Err(AsmError { kind: $kind, pos: $pos, line: $line, line_num: $line_num })
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
        let (instruction, header_aft) = match args.extract_header(&line) {
            Err(e) => return err!(e => line : args.line_num),
            Ok(v) => v,
        };
        debug_assert!(match line[header_aft..].chars().next() { Some(c) => c.is_whitespace() || c == COMMENT_CHAR, None => true });

        if let Some((name, _)) = &args.label_def {
            // label on a segment line would be ambiguous where label should go - end of previous segment or start of next
            if instruction == Some(Instruction::SEGMENT) { return err!(0, AsmErrorKind::LabelOnSegmentLine => line : args.line_num); }

            // equ defines its own symbol, otherwise it's a real label
            if instruction != Some(Instruction::EQU) {
                let val = match args.current_seg {
                    None => return err!(0, AsmErrorKind::LabelOutsideOfSegment => line : args.line_num),
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
                if let Err(_) = args.file.symbols.define(name.clone(), val) {
                    return err!(0, AsmErrorKind::SymbolAlreadyDefined => line : args.line_num);
                }
            }
        }

        // if times count is zero, we shouldn't even look at the rest of the line
        let instruction = match instruction {
            None => {
                debug_assert!(args.times.is_none()); // this is a syntax error, and should be handled elsewhere
                continue; // if there's not an instruction on this line, we also don't have to do anything
            }
            Some(x) => x,
        };
        if let Some(TimesInfo { total_count: 0, current: _ }) = args.times { continue; }
        loop { // otherwise we have to parse it once each time and update the times iter count after each step (if applicable)
            let res = match instruction { // then we proceed into the handlers
                Instruction::SEGMENT => {
                    let (seg, seg_aft) = grab_whitespace_sep_token(&line, header_aft, line.len());
                    if seg.is_empty() { return err!(0, AsmErrorKind::IncorrectArgCount(1) => line : args.line_num); }
                    let seg = match SEGMENTS.get(&Caseless(seg)) {
                        None => return err!(0, AsmErrorKind::UnrecognizedSegment => line : args.line_num),
                        Some(seg) => *seg,
                    };
                    if args.done_segs.contains(&seg) { return err!(0, AsmErrorKind::SegmentAlreadyCompleted => line : args.line_num); }
                    args.done_segs.push(seg);
                    args.current_seg = Some(seg);

                    // make sure we didn't have extra stuff after the segment name
                    let (tok, _) = grab_whitespace_sep_token(&line, seg_aft, line.len());
                    if !tok.is_empty() { return err!(0, AsmErrorKind::ExtraContentAfterSegmentName => line : args.line_num); }

                    Ok(())
                }
                _ => { // all the non-prefix ops are handled here to avoid duping the arg parsing code in every handler
                    let arguments = match args.extract_arguments(&line, header_aft) {
                        Err(e) => return err!(e => line : args.line_num),
                        Ok(x) => x,
                    };
                    match instruction {
                        Instruction::EQU => match &args.label_def {
                            None => return err!(0, AsmErrorKind::EQUWithoutLabel => line : args.line_num),
                            Some((name, _)) => {
                                if arguments.len() != 1 {
                                    return err!(0, AsmErrorKind::IncorrectArgCount(1) => line : args.line_num);
                                }
                                let val = match arguments.into_iter().next().unwrap() {
                                    Argument::Imm(imm) => {
                                        if let Some(_) = imm.size {
                                            return err!(0, AsmErrorKind::EQUArgumentHadSizeSpec => line : args.line_num);
                                        }
                                        imm.expr
                                    }
                                    _ => return err!(0, AsmErrorKind::ExpectedExpressionArg(0) => line : args.line_num),
                                };
                                if let Err(_) = args.file.symbols.define(name.into(), val) {
                                    return err!(0, AsmErrorKind::SymbolAlreadyDefined => line : args.line_num);
                                }
                                Ok(())
                            }
                        }
                        Instruction::SEGMENT => unreachable!(), // handled above
                        Instruction::NOP => args.process_no_arg_op(arguments, Some(OPCode::NOP as u8), None),

                        Instruction::MOV => args.process_binary_op(arguments, OPCode::MOV as u8, None, HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),

                        Instruction::MOVZ => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(0), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVNZ => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(1), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVS => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(2), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVNS => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(3), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVP => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(4), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVNP => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(5), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVO => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(6), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVNO => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(7), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVC => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(8), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVNC => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(9), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVB => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(10), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVBE => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(11), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVA => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(12), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVAE => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(13), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVL => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(14), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVLE => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(15), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVG => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(16), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                        Instruction::MOVGE => args.process_binary_op(arguments, OPCode::MOVcc as u8, Some(17), HoleType::Integral, &[Size::Byte, Size::Word, Size::Dword, Size::Qword], None),
                    }
                }
            };
            if let Err(e) = res { // process any errors we got from the handler
                return err!(e => line : args.line_num);
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

    Ok(args.file)
}