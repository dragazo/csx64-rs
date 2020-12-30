use std::collections::{HashMap, BTreeMap, BTreeSet};

use super::expr::*;
use super::{Size, AsmSegment};
use super::caseless::Caseless;

macro_rules! insert {
    ($m:ident : $key:expr => $val:expr) => {
        assert!($m.insert($key, $val).is_none())
    };
    ($s:ident : $val:expr) => {
        assert!($s.insert($val))
    }
}
macro_rules! alias {
    ($m:ident : $from:expr => $to:expr) => {{
        let v = *$m.get(&$to).unwrap();
        insert!($m: $from => v);
    }}
}

pub(super) const COMMENT_CHAR: char = ';';
pub(super) const LABEL_DEF_CHAR: char = ':';

pub(super) const MAX_ALIGN: u64 = 1024;

// these must be ordered in descending order of length to parse correctly (hence array)
pub(super) const BINARY_OP_STR: &'static[(&'static str, OP)] = &[
    ("<<", OP::SHL),
    (">>", OP::SHR),
    ("==", OP::Equ),
    ("!=", OP::Neq),
    ("<=", OP::LessE),
    (">=", OP::GreatE),

    ("*", OP::Mul),
    ("/", OP::Div),
    ("%", OP::Mod),
    ("+", OP::Add),
    ("-", OP::Sub),
    ("<", OP::Less),
    (">", OP::Great),
    ("&", OP::And),
    ("^", OP::Xor),
    ("|", OP::Or),
];

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Associativity {
    Left, //Right, // currently everything we support is left associative, but maybe that'll change at some point
}

lazy_static! {
    pub(super) static ref PRECEDENCE: HashMap<OP, (i32, Associativity)> = {
        let mut m = HashMap::new();
        
        insert!(m: OP::Mul => (5, Associativity::Left));

        insert!(m: OP::Div => (5, Associativity::Left));
        insert!(m: OP::Mod => (5, Associativity::Left));

        insert!(m: OP::Add => (6, Associativity::Left));
        insert!(m: OP::Sub => (6, Associativity::Left));

        insert!(m: OP::SHL => (7, Associativity::Left));
        insert!(m: OP::SHR => (7, Associativity::Left));

        insert!(m: OP::Less => (9, Associativity::Left));
        insert!(m: OP::LessE => (9, Associativity::Left));
        insert!(m: OP::Great => (9, Associativity::Left));
        insert!(m: OP::GreatE => (9, Associativity::Left));

        insert!(m: OP::Equ => (10, Associativity::Left));
        insert!(m: OP::Neq => (10, Associativity::Left));

        insert!(m: OP::And => (11, Associativity::Left));
        insert!(m: OP::Xor => (12, Associativity::Left));
        insert!(m: OP::Or => (13, Associativity::Left));

        m
    };
}

lazy_static! {
    pub(super) static ref UNARY_FUNCTION_OPERATOR_TO_OP: HashMap<&'static str, OP> = {
        let mut m = HashMap::new();

        // m.insert("$INT", OP::Int);
        // m.insert("$UINT", OP::UInt);
        // m.insert("$FLOAT", OP::Float);

        // m.insert("$FLOOR", OP::Floor);
        // m.insert("$CEIL", OP::Ceil);
        // m.insert("$ROUND", OP::Round);
        // m.insert("$TRUNC", OP::Trunc);

        // m.insert("$REPR64", OP::Repr64);
        // m.insert("$REPR32", OP::Repr32);

        // m.insert("$FLOAT64", OP::Float64);
        // m.insert("$FLOAT32", OP::Float32);

        // m.insert("$PREC64", OP::Prec64);
        // m.insert("$PREC32", OP::Prec32);

        m
    };
}

pub(super) fn get_seg_offset_str(seg: AsmSegment) -> &'static str {
    match seg {
        AsmSegment::Text => "#t",
        AsmSegment::Rodata => "#r",
        AsmSegment::Data => "#d",
        AsmSegment::Bss => "#b",
    }
}
pub(super) fn get_seg_origin_str(seg: AsmSegment) -> &'static str {
    match seg {
        AsmSegment::Text => "#T",
        AsmSegment::Rodata => "#R",
        AsmSegment::Data => "#D",
        AsmSegment::Bss => "#B",
    }
}

pub(super) const BINARY_LITERAL_SYMBOL_PREFIX: &str = "#L";

pub(super) const PTRDIFF_IDS: &[&'static str] = &["#t", "#r", "#d", "#b", "#T", "#R", "#D", "#B"];

lazy_static! {
    pub(super) static ref SIZE_KEYWORDS: BTreeMap<Caseless<'static>, Size> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("BYTE") => Size::Byte);
        insert!(m: Caseless("WORD") => Size::Word);
        insert!(m: Caseless("DWORD") => Size::Dword);
        insert!(m: Caseless("QWORD") => Size::Qword);
        insert!(m: Caseless("XWORD") => Size::Xword);
        insert!(m: Caseless("YWORD") => Size::Yword);
        insert!(m: Caseless("ZWORD") => Size::Zword);
        insert!(m: Caseless("TWORD") => Size::Tword);

        m
    };
}

#[derive(Clone, Copy, Debug)]
pub(super) struct CPURegisterInfo {
    pub(super) id: u8,
    pub(super) size: Size,
    pub(super) high: bool,
}
lazy_static! {
    pub(super) static ref CPU_REGISTER_INFO: BTreeMap<Caseless<'static>, CPURegisterInfo> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("RAX") => CPURegisterInfo { id: 0, size: Size::Qword, high: false });
        insert!(m: Caseless("RBX") => CPURegisterInfo { id: 1, size: Size::Qword, high: false });
        insert!(m: Caseless("RCX") => CPURegisterInfo { id: 2, size: Size::Qword, high: false });
        insert!(m: Caseless("RDX") => CPURegisterInfo { id: 3, size: Size::Qword, high: false });
        insert!(m: Caseless("RSI") => CPURegisterInfo { id: 4, size: Size::Qword, high: false });
        insert!(m: Caseless("RDI") => CPURegisterInfo { id: 5, size: Size::Qword, high: false });
        insert!(m: Caseless("RBP") => CPURegisterInfo { id: 6, size: Size::Qword, high: false });
        insert!(m: Caseless("RSP") => CPURegisterInfo { id: 7, size: Size::Qword, high: false });
        insert!(m: Caseless("R8") => CPURegisterInfo { id: 8, size: Size::Qword, high: false });
        insert!(m: Caseless("R9") => CPURegisterInfo { id: 9, size: Size::Qword, high: false });
        insert!(m: Caseless("R10") => CPURegisterInfo { id: 10, size: Size::Qword, high: false });
        insert!(m: Caseless("R11") => CPURegisterInfo { id: 11, size: Size::Qword, high: false });
        insert!(m: Caseless("R12") => CPURegisterInfo { id: 12, size: Size::Qword, high: false });
        insert!(m: Caseless("R13") => CPURegisterInfo { id: 13, size: Size::Qword, high: false });
        insert!(m: Caseless("R14") => CPURegisterInfo { id: 14, size: Size::Qword, high: false });
        insert!(m: Caseless("R15") => CPURegisterInfo { id: 15, size: Size::Qword, high: false });

        insert!(m: Caseless("EAX") => CPURegisterInfo { id: 0, size: Size::Dword, high: false });
        insert!(m: Caseless("EBX") => CPURegisterInfo { id: 1, size: Size::Dword, high: false });
        insert!(m: Caseless("ECX") => CPURegisterInfo { id: 2, size: Size::Dword, high: false });
        insert!(m: Caseless("EDX") => CPURegisterInfo { id: 3, size: Size::Dword, high: false });
        insert!(m: Caseless("ESI") => CPURegisterInfo { id: 4, size: Size::Dword, high: false });
        insert!(m: Caseless("EDI") => CPURegisterInfo { id: 5, size: Size::Dword, high: false });
        insert!(m: Caseless("EBP") => CPURegisterInfo { id: 6, size: Size::Dword, high: false });
        insert!(m: Caseless("ESP") => CPURegisterInfo { id: 7, size: Size::Dword, high: false });
        insert!(m: Caseless("R8D") => CPURegisterInfo { id: 8, size: Size::Dword, high: false });
        insert!(m: Caseless("R9D") => CPURegisterInfo { id: 9, size: Size::Dword, high: false });
        insert!(m: Caseless("R10D") => CPURegisterInfo { id: 10, size: Size::Dword, high: false });
        insert!(m: Caseless("R11D") => CPURegisterInfo { id: 11, size: Size::Dword, high: false });
        insert!(m: Caseless("R12D") => CPURegisterInfo { id: 12, size: Size::Dword, high: false });
        insert!(m: Caseless("R13D") => CPURegisterInfo { id: 13, size: Size::Dword, high: false });
        insert!(m: Caseless("R14D") => CPURegisterInfo { id: 14, size: Size::Dword, high: false });
        insert!(m: Caseless("R15D") => CPURegisterInfo { id: 15, size: Size::Dword, high: false });

        insert!(m: Caseless("AX") => CPURegisterInfo { id: 0, size: Size::Word, high: false });
        insert!(m: Caseless("BX") => CPURegisterInfo { id: 1, size: Size::Word, high: false });
        insert!(m: Caseless("CX") => CPURegisterInfo { id: 2, size: Size::Word, high: false });
        insert!(m: Caseless("DX") => CPURegisterInfo { id: 3, size: Size::Word, high: false });
        insert!(m: Caseless("SI") => CPURegisterInfo { id: 4, size: Size::Word, high: false });
        insert!(m: Caseless("DI") => CPURegisterInfo { id: 5, size: Size::Word, high: false });
        insert!(m: Caseless("BP") => CPURegisterInfo { id: 6, size: Size::Word, high: false });
        insert!(m: Caseless("SP") => CPURegisterInfo { id: 7, size: Size::Word, high: false });
        insert!(m: Caseless("R8W") => CPURegisterInfo { id: 8, size: Size::Word, high: false });
        insert!(m: Caseless("R9W") => CPURegisterInfo { id: 9, size: Size::Word, high: false });
        insert!(m: Caseless("R10W") => CPURegisterInfo { id: 10, size: Size::Word, high: false });
        insert!(m: Caseless("R11W") => CPURegisterInfo { id: 11, size: Size::Word, high: false });
        insert!(m: Caseless("R12W") => CPURegisterInfo { id: 12, size: Size::Word, high: false });
        insert!(m: Caseless("R13W") => CPURegisterInfo { id: 13, size: Size::Word, high: false });
        insert!(m: Caseless("R14W") => CPURegisterInfo { id: 14, size: Size::Word, high: false });
        insert!(m: Caseless("R15W") => CPURegisterInfo { id: 15, size: Size::Word, high: false });

        insert!(m: Caseless("AL") => CPURegisterInfo { id: 0, size: Size::Byte, high: false });
        insert!(m: Caseless("BL") => CPURegisterInfo { id: 1, size: Size::Byte, high: false });
        insert!(m: Caseless("CL") => CPURegisterInfo { id: 2, size: Size::Byte, high: false });
        insert!(m: Caseless("DL") => CPURegisterInfo { id: 3, size: Size::Byte, high: false });
        insert!(m: Caseless("SIL") => CPURegisterInfo { id: 4, size: Size::Byte, high: false });
        insert!(m: Caseless("DIL") => CPURegisterInfo { id: 5, size: Size::Byte, high: false });
        insert!(m: Caseless("BPL") => CPURegisterInfo { id: 6, size: Size::Byte, high: false });
        insert!(m: Caseless("SPL") => CPURegisterInfo { id: 7, size: Size::Byte, high: false });
        insert!(m: Caseless("R8B") => CPURegisterInfo { id: 8, size: Size::Byte, high: false });
        insert!(m: Caseless("R9B") => CPURegisterInfo { id: 9, size: Size::Byte, high: false });
        insert!(m: Caseless("R10B") => CPURegisterInfo { id: 10, size: Size::Byte, high: false });
        insert!(m: Caseless("R11B") => CPURegisterInfo { id: 11, size: Size::Byte, high: false });
        insert!(m: Caseless("R12B") => CPURegisterInfo { id: 12, size: Size::Byte, high: false });
        insert!(m: Caseless("R13B") => CPURegisterInfo { id: 13, size: Size::Byte, high: false });
        insert!(m: Caseless("R14B") => CPURegisterInfo { id: 14, size: Size::Byte, high: false });
        insert!(m: Caseless("R15B") => CPURegisterInfo { id: 15, size: Size::Byte, high: false });

        insert!(m: Caseless("AH") => CPURegisterInfo { id: 0, size: Size::Byte, high: true });
        insert!(m: Caseless("BH") => CPURegisterInfo { id: 1, size: Size::Byte, high: true });
        insert!(m: Caseless("CH") => CPURegisterInfo { id: 2, size: Size::Byte, high: true });
        insert!(m: Caseless("DH") => CPURegisterInfo { id: 3, size: Size::Byte, high: true });

        m
    };
}

#[derive(Clone, Copy, Debug)]
pub(super) struct FPURegisterInfo {
    pub(super) id: u8,
}
lazy_static! {
    pub(super) static ref FPU_REGISTER_INFO: BTreeMap<Caseless<'static>, FPURegisterInfo> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("ST") => FPURegisterInfo { id: 0 });

        insert!(m: Caseless("ST0") => FPURegisterInfo { id: 0 });
        insert!(m: Caseless("ST1") => FPURegisterInfo { id: 1 });
        insert!(m: Caseless("ST2") => FPURegisterInfo { id: 2 });
        insert!(m: Caseless("ST3") => FPURegisterInfo { id: 3 });
        insert!(m: Caseless("ST4") => FPURegisterInfo { id: 4 });
        insert!(m: Caseless("ST5") => FPURegisterInfo { id: 5 });
        insert!(m: Caseless("ST6") => FPURegisterInfo { id: 6 });
        insert!(m: Caseless("ST7") => FPURegisterInfo { id: 7 });

        m
    };
}

#[derive(Clone, Copy, Debug)]
pub(super) struct VPURegisterInfo {
    pub(super) id: u8,
    pub(super) size: Size,
}
lazy_static! {
    pub(super) static ref VPU_REGISTER_INFO: BTreeMap<Caseless<'static>, VPURegisterInfo> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("XMM0") => VPURegisterInfo { id: 0, size: Size::Xword });
        insert!(m: Caseless("XMM1") => VPURegisterInfo { id: 1, size: Size::Xword });
        insert!(m: Caseless("XMM2") => VPURegisterInfo { id: 2, size: Size::Xword });
        insert!(m: Caseless("XMM3") => VPURegisterInfo { id: 3, size: Size::Xword });
        insert!(m: Caseless("XMM4") => VPURegisterInfo { id: 4, size: Size::Xword });
        insert!(m: Caseless("XMM5") => VPURegisterInfo { id: 5, size: Size::Xword });
        insert!(m: Caseless("XMM6") => VPURegisterInfo { id: 6, size: Size::Xword });
        insert!(m: Caseless("XMM7") => VPURegisterInfo { id: 7, size: Size::Xword });
        insert!(m: Caseless("XMM8") => VPURegisterInfo { id: 8, size: Size::Xword });
        insert!(m: Caseless("XMM9") => VPURegisterInfo { id: 9, size: Size::Xword });
        insert!(m: Caseless("XMM10") => VPURegisterInfo { id: 10, size: Size::Xword });
        insert!(m: Caseless("XMM11") => VPURegisterInfo { id: 11, size: Size::Xword });
        insert!(m: Caseless("XMM12") => VPURegisterInfo { id: 12, size: Size::Xword });
        insert!(m: Caseless("XMM13") => VPURegisterInfo { id: 13, size: Size::Xword });
        insert!(m: Caseless("XMM14") => VPURegisterInfo { id: 14, size: Size::Xword });
        insert!(m: Caseless("XMM15") => VPURegisterInfo { id: 15, size: Size::Xword });

        insert!(m: Caseless("YMM0") => VPURegisterInfo { id: 0, size: Size::Yword });
        insert!(m: Caseless("YMM1") => VPURegisterInfo { id: 1, size: Size::Yword });
        insert!(m: Caseless("YMM2") => VPURegisterInfo { id: 2, size: Size::Yword });
        insert!(m: Caseless("YMM3") => VPURegisterInfo { id: 3, size: Size::Yword });
        insert!(m: Caseless("YMM4") => VPURegisterInfo { id: 4, size: Size::Yword });
        insert!(m: Caseless("YMM5") => VPURegisterInfo { id: 5, size: Size::Yword });
        insert!(m: Caseless("YMM6") => VPURegisterInfo { id: 6, size: Size::Yword });
        insert!(m: Caseless("YMM7") => VPURegisterInfo { id: 7, size: Size::Yword });
        insert!(m: Caseless("YMM8") => VPURegisterInfo { id: 8, size: Size::Yword });
        insert!(m: Caseless("YMM9") => VPURegisterInfo { id: 9, size: Size::Yword });
        insert!(m: Caseless("YMM10") => VPURegisterInfo { id: 10, size: Size::Yword });
        insert!(m: Caseless("YMM11") => VPURegisterInfo { id: 11, size: Size::Yword });
        insert!(m: Caseless("YMM12") => VPURegisterInfo { id: 12, size: Size::Yword });
        insert!(m: Caseless("YMM13") => VPURegisterInfo { id: 13, size: Size::Yword });
        insert!(m: Caseless("YMM14") => VPURegisterInfo { id: 14, size: Size::Yword });
        insert!(m: Caseless("YMM15") => VPURegisterInfo { id: 15, size: Size::Yword });

        insert!(m: Caseless("ZMM0") => VPURegisterInfo { id: 0, size: Size::Zword });
        insert!(m: Caseless("ZMM1") => VPURegisterInfo { id: 1, size: Size::Zword });
        insert!(m: Caseless("ZMM2") => VPURegisterInfo { id: 2, size: Size::Zword });
        insert!(m: Caseless("ZMM3") => VPURegisterInfo { id: 3, size: Size::Zword });
        insert!(m: Caseless("ZMM4") => VPURegisterInfo { id: 4, size: Size::Zword });
        insert!(m: Caseless("ZMM5") => VPURegisterInfo { id: 5, size: Size::Zword });
        insert!(m: Caseless("ZMM6") => VPURegisterInfo { id: 6, size: Size::Zword });
        insert!(m: Caseless("ZMM7") => VPURegisterInfo { id: 7, size: Size::Zword });
        insert!(m: Caseless("ZMM8") => VPURegisterInfo { id: 8, size: Size::Zword });
        insert!(m: Caseless("ZMM9") => VPURegisterInfo { id: 9, size: Size::Zword });
        insert!(m: Caseless("ZMM10") => VPURegisterInfo { id: 10, size: Size::Zword });
        insert!(m: Caseless("ZMM11") => VPURegisterInfo { id: 11, size: Size::Zword });
        insert!(m: Caseless("ZMM12") => VPURegisterInfo { id: 12, size: Size::Zword });
        insert!(m: Caseless("ZMM13") => VPURegisterInfo { id: 13, size: Size::Zword });
        insert!(m: Caseless("ZMM14") => VPURegisterInfo { id: 14, size: Size::Zword });
        insert!(m: Caseless("ZMM15") => VPURegisterInfo { id: 15, size: Size::Zword });
        insert!(m: Caseless("ZMM16") => VPURegisterInfo { id: 16, size: Size::Zword });
        insert!(m: Caseless("ZMM17") => VPURegisterInfo { id: 17, size: Size::Zword });
        insert!(m: Caseless("ZMM18") => VPURegisterInfo { id: 18, size: Size::Zword });
        insert!(m: Caseless("ZMM19") => VPURegisterInfo { id: 19, size: Size::Zword });
        insert!(m: Caseless("ZMM20") => VPURegisterInfo { id: 20, size: Size::Zword });
        insert!(m: Caseless("ZMM21") => VPURegisterInfo { id: 21, size: Size::Zword });
        insert!(m: Caseless("ZMM22") => VPURegisterInfo { id: 22, size: Size::Zword });
        insert!(m: Caseless("ZMM23") => VPURegisterInfo { id: 23, size: Size::Zword });
        insert!(m: Caseless("ZMM24") => VPURegisterInfo { id: 24, size: Size::Zword });
        insert!(m: Caseless("ZMM25") => VPURegisterInfo { id: 25, size: Size::Zword });
        insert!(m: Caseless("ZMM26") => VPURegisterInfo { id: 26, size: Size::Zword });
        insert!(m: Caseless("ZMM27") => VPURegisterInfo { id: 27, size: Size::Zword });
        insert!(m: Caseless("ZMM28") => VPURegisterInfo { id: 28, size: Size::Zword });
        insert!(m: Caseless("ZMM29") => VPURegisterInfo { id: 29, size: Size::Zword });
        insert!(m: Caseless("ZMM30") => VPURegisterInfo { id: 30, size: Size::Zword });
        insert!(m: Caseless("ZMM31") => VPURegisterInfo { id: 31, size: Size::Zword });

        m
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Prefix {
    REP, REPZ, REPNZ,
    LOCK,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Instruction {
    EQU,
    SEGMENT,
    GLOBAL, EXTERN,
    ALIGN,
    ASSERT,
    DECLARE(Size), RESERVE(Size),
    NOP, HLT, SYSCALL,
    LFENCE, SFENCE, MFENCE,
    MOV, MOVcc(u8), SETcc(u8), LEA, XCHG,
    FLAGBIT(u8),
    ADD, SUB, CMP,
    AND, OR, XOR, TEST,
    SHIFT(u8), SHIFTX(u8), BTX(u8),
    MUL, IMUL, MULX, IMULX, DIV, IDIV,
    JMP, Jcc(u8), LOOPcc(u8), CALL, RET,
    PUSH, POP,
    INC, DEC, NEG, NOT,
    MOVS(Size), STOS(Size),
    DEBUG(u8),
}

lazy_static! {
    pub(super) static ref PREFIXES: BTreeMap<Caseless<'static>, Prefix> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("REP") => Prefix::REP);
        insert!(m: Caseless("REPZ") => Prefix::REPZ);
        insert!(m: Caseless("REPNZ") => Prefix::REPNZ);

        alias!(m: Caseless("REPE") => Caseless("REPZ"));
        alias!(m: Caseless("REPNE") => Caseless("REPNZ"));

        insert!(m: Caseless("LOCK") => Prefix::LOCK);

        m
    };
    pub(super) static ref INSTRUCTIONS: BTreeMap<Caseless<'static>, Instruction> = {
        let mut m = BTreeMap::new();
        
        insert!(m: Caseless("EQU") => Instruction::EQU);
        insert!(m: Caseless("SEGMENT") => Instruction::SEGMENT);

        insert!(m: Caseless("GLOBAL") => Instruction::GLOBAL);
        insert!(m: Caseless("EXTERN") => Instruction::EXTERN);

        insert!(m: Caseless("ALIGN") => Instruction::ALIGN);

        insert!(m: Caseless("STATIC_ASSERT") => Instruction::ASSERT);
        
        insert!(m: Caseless("DB") => Instruction::DECLARE(Size::Byte));
        insert!(m: Caseless("DW") => Instruction::DECLARE(Size::Word));
        insert!(m: Caseless("DD") => Instruction::DECLARE(Size::Dword));
        insert!(m: Caseless("DQ") => Instruction::DECLARE(Size::Qword));
        insert!(m: Caseless("DX") => Instruction::DECLARE(Size::Xword));
        insert!(m: Caseless("DY") => Instruction::DECLARE(Size::Yword));
        insert!(m: Caseless("DZ") => Instruction::DECLARE(Size::Zword));
        insert!(m: Caseless("DT") => Instruction::DECLARE(Size::Tword));

        insert!(m: Caseless("RESB") => Instruction::RESERVE(Size::Byte));
        insert!(m: Caseless("RESW") => Instruction::RESERVE(Size::Word));
        insert!(m: Caseless("RESD") => Instruction::RESERVE(Size::Dword));
        insert!(m: Caseless("RESQ") => Instruction::RESERVE(Size::Qword));
        insert!(m: Caseless("RESX") => Instruction::RESERVE(Size::Xword));
        insert!(m: Caseless("RESY") => Instruction::RESERVE(Size::Yword));
        insert!(m: Caseless("RESZ") => Instruction::RESERVE(Size::Zword));
        insert!(m: Caseless("REST") => Instruction::RESERVE(Size::Tword));

        insert!(m: Caseless("NOP") => Instruction::NOP);
        insert!(m: Caseless("HLT") => Instruction::HLT);
        insert!(m: Caseless("SYSCALL") => Instruction::SYSCALL);

        alias!(m: Caseless("PAUSE") => Caseless("HLT"));

        insert!(m: Caseless("LFENCE") => Instruction::LFENCE);
        insert!(m: Caseless("SFENCE") => Instruction::SFENCE);
        insert!(m: Caseless("MFENCE") => Instruction::MFENCE);
        
        insert!(m: Caseless("MOV") => Instruction::MOV);
        
        insert!(m: Caseless("MOVZ") => Instruction::MOVcc(0));
        insert!(m: Caseless("MOVNZ") => Instruction::MOVcc(1));
        insert!(m: Caseless("MOVS") => Instruction::MOVcc(2));
        insert!(m: Caseless("MOVNS") => Instruction::MOVcc(3));
        insert!(m: Caseless("MOVP") => Instruction::MOVcc(4));
        insert!(m: Caseless("MOVNP") => Instruction::MOVcc(5));
        insert!(m: Caseless("MOVO") => Instruction::MOVcc(6));
        insert!(m: Caseless("MOVNO") => Instruction::MOVcc(7));
        insert!(m: Caseless("MOVC") => Instruction::MOVcc(8));
        insert!(m: Caseless("MOVNC") => Instruction::MOVcc(9));
        insert!(m: Caseless("MOVB") => Instruction::MOVcc(10));
        insert!(m: Caseless("MOVBE") => Instruction::MOVcc(11));
        insert!(m: Caseless("MOVA") => Instruction::MOVcc(12));
        insert!(m: Caseless("MOVAE") => Instruction::MOVcc(13));
        insert!(m: Caseless("MOVL") => Instruction::MOVcc(14));
        insert!(m: Caseless("MOVLE") => Instruction::MOVcc(15));
        insert!(m: Caseless("MOVG") => Instruction::MOVcc(16));
        insert!(m: Caseless("MOVGE") => Instruction::MOVcc(17));

        alias!(m: Caseless("MOVE") => Caseless("MOVZ"));
        alias!(m: Caseless("MOVNE") => Caseless("MOVNZ"));
        alias!(m: Caseless("MOVPE") => Caseless("MOVP"));
        alias!(m: Caseless("MOVPO") => Caseless("MOVNP"));
        alias!(m: Caseless("MOVNAE") => Caseless("MOVB"));
        alias!(m: Caseless("MOVNA") => Caseless("MOVBE"));
        alias!(m: Caseless("MOVNBE") => Caseless("MOVA"));
        alias!(m: Caseless("MOVNB") => Caseless("MOVAE"));
        alias!(m: Caseless("MOVNGE") => Caseless("MOVL"));
        alias!(m: Caseless("MOVNG") => Caseless("MOVLE"));
        alias!(m: Caseless("MOVNLE") => Caseless("MOVG"));
        alias!(m: Caseless("MOVNL") => Caseless("MOVGE"));
        
        insert!(m: Caseless("LEA") => Instruction::LEA);
        insert!(m: Caseless("XCHG") => Instruction::XCHG);

        insert!(m: Caseless("SETZ") => Instruction::SETcc(0));
        insert!(m: Caseless("SETNZ") => Instruction::SETcc(1));
        insert!(m: Caseless("SETS") => Instruction::SETcc(2));
        insert!(m: Caseless("SETNS") => Instruction::SETcc(3));
        insert!(m: Caseless("SETP") => Instruction::SETcc(4));
        insert!(m: Caseless("SETNP") => Instruction::SETcc(5));
        insert!(m: Caseless("SETO") => Instruction::SETcc(6));
        insert!(m: Caseless("SETNO") => Instruction::SETcc(7));
        insert!(m: Caseless("SETC") => Instruction::SETcc(8));
        insert!(m: Caseless("SETNC") => Instruction::SETcc(9));
        insert!(m: Caseless("SETB") => Instruction::SETcc(10));
        insert!(m: Caseless("SETBE") => Instruction::SETcc(11));
        insert!(m: Caseless("SETA") => Instruction::SETcc(12));
        insert!(m: Caseless("SETAE") => Instruction::SETcc(13));
        insert!(m: Caseless("SETL") => Instruction::SETcc(14));
        insert!(m: Caseless("SETLE") => Instruction::SETcc(15));
        insert!(m: Caseless("SETG") => Instruction::SETcc(16));
        insert!(m: Caseless("SETGE") => Instruction::SETcc(17));

        alias!(m: Caseless("SETE") => Caseless("SETZ"));
        alias!(m: Caseless("SETNE") => Caseless("SETNZ"));
        alias!(m: Caseless("SETPE") => Caseless("SETP"));
        alias!(m: Caseless("SETPO") => Caseless("SETNP"));
        alias!(m: Caseless("SETNAE") => Caseless("SETB"));
        alias!(m: Caseless("SETNA") => Caseless("SETBE"));
        alias!(m: Caseless("SETBNE") => Caseless("SETA"));
        alias!(m: Caseless("SETNB") => Caseless("SETAE"));
        alias!(m: Caseless("SETNGE") => Caseless("SETL"));
        alias!(m: Caseless("SETNG") => Caseless("SETLE"));
        alias!(m: Caseless("SETNLE") => Caseless("SETG"));
        alias!(m: Caseless("SETNL") => Caseless("SETGE"));

        insert!(m: Caseless("STAC") => Instruction::FLAGBIT(0));
        insert!(m: Caseless("CLAC") => Instruction::FLAGBIT(1));
        insert!(m: Caseless("CMAC") => Instruction::FLAGBIT(2));
        insert!(m: Caseless("STC") => Instruction::FLAGBIT(3));
        insert!(m: Caseless("CLC") => Instruction::FLAGBIT(4));
        insert!(m: Caseless("CMC") => Instruction::FLAGBIT(5));
        insert!(m: Caseless("STD") => Instruction::FLAGBIT(6));
        insert!(m: Caseless("CLD") => Instruction::FLAGBIT(7));
        insert!(m: Caseless("CMD") => Instruction::FLAGBIT(8));
        insert!(m: Caseless("STI") => Instruction::FLAGBIT(9));
        insert!(m: Caseless("CLI") => Instruction::FLAGBIT(10));
        insert!(m: Caseless("CMI") => Instruction::FLAGBIT(11));

        insert!(m: Caseless("ADD") => Instruction::ADD);
        insert!(m: Caseless("SUB") => Instruction::SUB);
        insert!(m: Caseless("CMP") => Instruction::CMP);

        insert!(m: Caseless("AND") => Instruction::AND);
        insert!(m: Caseless("OR") => Instruction::OR);
        insert!(m: Caseless("XOR") => Instruction::XOR);
        insert!(m: Caseless("TEST") => Instruction::TEST);

        insert!(m: Caseless("SHL") => Instruction::SHIFT(0));
        insert!(m: Caseless("SHR") => Instruction::SHIFT(1));
        insert!(m: Caseless("SAR") => Instruction::SHIFT(2));
        
        insert!(m: Caseless("ROL") => Instruction::SHIFT(3));
        insert!(m: Caseless("ROR") => Instruction::SHIFT(4));
        insert!(m: Caseless("RCL") => Instruction::SHIFT(5));
        insert!(m: Caseless("RCR") => Instruction::SHIFT(6));

        insert!(m: Caseless("SHLX") => Instruction::SHIFTX(7));
        insert!(m: Caseless("SHRX") => Instruction::SHIFTX(8));
        insert!(m: Caseless("SARX") => Instruction::SHIFTX(9));

        alias!(m: Caseless("SAL") => Caseless("SHL"));
        alias!(m: Caseless("SALX") => Caseless("SHLX"));

        insert!(m: Caseless("BT") => Instruction::BTX(10));
        insert!(m: Caseless("BTC") => Instruction::BTX(11));
        insert!(m: Caseless("BTR") => Instruction::BTX(12));
        insert!(m: Caseless("BTS") => Instruction::BTX(13));

        insert!(m: Caseless("MUL") => Instruction::MUL);
        insert!(m: Caseless("IMUL") => Instruction::IMUL);
        insert!(m: Caseless("MULX") => Instruction::MULX);
        insert!(m: Caseless("IMULX") => Instruction::IMULX);

        insert!(m: Caseless("DIV") => Instruction::DIV);
        insert!(m: Caseless("IDIV") => Instruction::IDIV);

        insert!(m: Caseless("JMP") => Instruction::JMP);

        insert!(m: Caseless("JZ") => Instruction::Jcc(0));
        insert!(m: Caseless("JNZ") => Instruction::Jcc(1));
        insert!(m: Caseless("JS") => Instruction::Jcc(2));
        insert!(m: Caseless("JNS") => Instruction::Jcc(3));
        insert!(m: Caseless("JP") => Instruction::Jcc(4));
        insert!(m: Caseless("JNP") => Instruction::Jcc(5));
        insert!(m: Caseless("JO") => Instruction::Jcc(6));
        insert!(m: Caseless("JNO") => Instruction::Jcc(7));
        insert!(m: Caseless("JC") => Instruction::Jcc(8));
        insert!(m: Caseless("JNC") => Instruction::Jcc(9));
        insert!(m: Caseless("JB") => Instruction::Jcc(10));
        insert!(m: Caseless("JBE") => Instruction::Jcc(11));
        insert!(m: Caseless("JA") => Instruction::Jcc(12));
        insert!(m: Caseless("JAE") => Instruction::Jcc(13));
        insert!(m: Caseless("JL") => Instruction::Jcc(14));
        insert!(m: Caseless("JLE") => Instruction::Jcc(15));
        insert!(m: Caseless("JG") => Instruction::Jcc(16));
        insert!(m: Caseless("JGE") => Instruction::Jcc(17));
        insert!(m: Caseless("JCXZ") => Instruction::Jcc(18));
        insert!(m: Caseless("JECXZ") => Instruction::Jcc(19));
        insert!(m: Caseless("JRCXZ") => Instruction::Jcc(20));

        alias!(m: Caseless("JE") => Caseless("JZ"));
        alias!(m: Caseless("JNE") => Caseless("JNZ"));
        alias!(m: Caseless("JPE") => Caseless("JP"));
        alias!(m: Caseless("JPO") => Caseless("JNP"));
        alias!(m: Caseless("JNAE") => Caseless("JB"));
        alias!(m: Caseless("JNA") => Caseless("JBE"));
        alias!(m: Caseless("JNBE") => Caseless("JA"));
        alias!(m: Caseless("JNB") => Caseless("JAE"));
        alias!(m: Caseless("JNGE") => Caseless("JL"));
        alias!(m: Caseless("JNG") => Caseless("JLE"));
        alias!(m: Caseless("JNLE") => Caseless("JG"));
        alias!(m: Caseless("JNL") => Caseless("JGE"));

        insert!(m: Caseless("LOOP") => Instruction::LOOPcc(0));
        insert!(m: Caseless("LOOPZ") => Instruction::LOOPcc(1));
        insert!(m: Caseless("LOOPNZ") => Instruction::LOOPcc(2));

        alias!(m: Caseless("LOOPE") => Caseless("LOOPZ"));
        alias!(m: Caseless("LOOPNE") => Caseless("LOOPNZ"));

        insert!(m: Caseless("CALL") => Instruction::CALL);
        insert!(m: Caseless("RET") => Instruction::RET);

        insert!(m: Caseless("PUSH") => Instruction::PUSH);
        insert!(m: Caseless("POP") => Instruction::POP);

        insert!(m: Caseless("INC") => Instruction::INC);
        insert!(m: Caseless("DEC") => Instruction::DEC);
        insert!(m: Caseless("NEG") => Instruction::NEG);
        insert!(m: Caseless("NOT") => Instruction::NOT);

        insert!(m: Caseless("MOVSB") => Instruction::MOVS(Size::Byte));
        insert!(m: Caseless("MOVSW") => Instruction::MOVS(Size::Word));
        insert!(m: Caseless("MOVSD") => Instruction::MOVS(Size::Dword));
        insert!(m: Caseless("MOVSQ") => Instruction::MOVS(Size::Qword));

        insert!(m: Caseless("STOSB") => Instruction::STOS(Size::Byte));
        insert!(m: Caseless("STOSW") => Instruction::STOS(Size::Word));
        insert!(m: Caseless("STOSD") => Instruction::STOS(Size::Dword));
        insert!(m: Caseless("STOSQ") => Instruction::STOS(Size::Qword));

        insert!(m: Caseless("DEBUG_CPU") => Instruction::DEBUG(0));

        m
    };
}

lazy_static! {
    pub(super) static ref SEGMENTS: BTreeMap<Caseless<'static>, AsmSegment> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("TEXT") => AsmSegment::Text);
        insert!(m: Caseless("RODATA") => AsmSegment::Rodata);
        insert!(m: Caseless("DATA") => AsmSegment::Data);
        insert!(m: Caseless("BSS") => AsmSegment::Bss);

        m
    };
}

lazy_static! {
    pub(super) static ref RESERVED_SYMBOLS: BTreeSet<Caseless<'static>> = {
        let mut s = BTreeSet::new();

        insert!(s: Caseless("IF"));
        insert!(s: Caseless("TIMES"));

        insert!(s: Caseless("TRUE"));
        insert!(s: Caseless("FALSE"));
        insert!(s: Caseless("NULL"));

        insert!(s: Caseless("PTR"));

        s.extend(SIZE_KEYWORDS.keys().copied());
        s.extend(CPU_REGISTER_INFO.keys().copied());
        s.extend(FPU_REGISTER_INFO.keys().copied());
        s.extend(VPU_REGISTER_INFO.keys().copied());
        s.extend(SEGMENTS.keys().copied());
        s.extend(PREFIXES.keys().copied());
        s.extend(INSTRUCTIONS.keys().copied());

        s
    };
}