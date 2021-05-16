use std::collections::{HashMap, BTreeMap, BTreeSet};

use super::expr::*;
use super::{Size, AsmSegment, HoleType};
use super::caseless::Caseless;
use crate::common::OPCode;

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
macro_rules! suggest {
    ($m:ident : $from:expr => [$($to:expr),+]) => {{
        let from = $from;
        const TO: &'static [Caseless<'static>] = &[$($to),+];
        for x in TO { assert!($m.get(x).is_some()); }
        insert!($m: from => Instruction::Suggest { from, to: TO });
    }}
}

pub(super) const COMMENT_CHAR: char = ';';
pub(super) const LABEL_DEF_CHAR: char = ':';

pub(super) const MAX_ALIGN: u64 = 1024;
pub(super) const MAX_RESERVE: u64 = u32::MAX as u64;

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
    pub(super) static ref UNARY_FUNCTION_OPERATOR_TO_OP: BTreeMap<&'static str, OP> = {
        let mut m = BTreeMap::new();

        insert!(m: "$len" => OP::Length);
        
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

pub(super) const BINARY_LITERAL_SYMBOL_PREFIX: &'static str = "#L";

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
pub(super) struct VPUMaskRegisterInfo {
    pub(super) id: u8,
}
lazy_static! {
    pub(super) static ref VPU_MASK_REGISTER_INFO: BTreeMap<Caseless<'static>, VPUMaskRegisterInfo> = {
        let mut m = BTreeMap::new();

        insert!(m: Caseless("K0") => VPUMaskRegisterInfo { id: 0 });
        insert!(m: Caseless("K1") => VPUMaskRegisterInfo { id: 1 });
        insert!(m: Caseless("K2") => VPUMaskRegisterInfo { id: 2 });
        insert!(m: Caseless("K3") => VPUMaskRegisterInfo { id: 3 });
        insert!(m: Caseless("K4") => VPUMaskRegisterInfo { id: 4 });
        insert!(m: Caseless("K5") => VPUMaskRegisterInfo { id: 5 });
        insert!(m: Caseless("K6") => VPUMaskRegisterInfo { id: 6 });
        insert!(m: Caseless("K7") => VPUMaskRegisterInfo { id: 7 });

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
    EQU, ASSERT,
    SEGMENT,
    GLOBAL, EXTERN,
    ALIGN, DECLARE(Size), RESERVE(Size),
    LEA, CMP,
    MUL, IMUL,
    MOVS(Size), STOS(Size),

    NoArg { op: Option<u8>, ext_op: Option<u8> },
    Unary { op: u8, ext_op: Option<u8>, allowed_sizes: &'static [Size] },
    Binary { op: u8, ext_op: Option<u8>, allowed_type: HoleType, allowed_sizes: &'static [Size], force_b_rm_size: Option<Size>, force_b_imm_size: Option<Size> },
    BinaryLvalueUnord { op: u8, ext_op: Option<u8>, allowed_sizes: &'static [Size] },
    Ternary { op: u8, ext_op: Option<u8>, allowed_type: HoleType, allowed_sizes: &'static [Size], force_b_rm_size: Option<Size>, force_b_imm_size: Option<Size> },
    Value { op: u8, ext_op: Option<u8>, allowed_type: HoleType, allowed_sizes: &'static [Size], default_size: Option<Size> },

    FPUBinary { op: u8, ext_op: Option<u8>, int: bool, pop: bool },
    FPUValue { op: u8, ext_op: Option<u8>, int: bool },

    VPUKMove { size: Size },
    VPUMove { elem_size: Option<Size>, packed: bool, aligned: bool },
    VPUBinary { op: u8, ext_op: Option<u8>, elem_size: Size, packed: bool },
    
    Suggest { from: Caseless<'static>, to: &'static [Caseless<'static>] },
}

pub(crate) const STANDARD_SIZES: &'static [Size] = &[Size::Byte, Size::Word, Size::Dword, Size::Qword];
pub(crate) const NON_BYTE_STANDARD_SIZES: &'static [Size] = &[Size::Word, Size::Dword, Size::Qword];

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

        insert!(m: Caseless("NOP") => Instruction::NoArg { op: Some(OPCode::NOP as u8), ext_op: None });
        insert!(m: Caseless("HLT") => Instruction::NoArg { op: Some(OPCode::HLT as u8), ext_op: None });
        insert!(m: Caseless("SYSCALL") => Instruction::NoArg { op: Some(OPCode::SYSCALL as u8), ext_op: None });

        alias!(m: Caseless("PAUSE") => Caseless("HLT"));

        insert!(m: Caseless("LFENCE") => Instruction::NoArg { op: None, ext_op: None });
        insert!(m: Caseless("SFENCE") => Instruction::NoArg { op: None, ext_op: None });
        insert!(m: Caseless("MFENCE") => Instruction::NoArg { op: None, ext_op: None });
        
        insert!(m: Caseless("MOV") => Instruction::Binary { op: OPCode::MOV as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        
        insert!(m: Caseless("CMOVZ") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(0), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVNZ") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(1), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVS") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(2), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVNS") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(3), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVP") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(4), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVNP") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(5), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVO") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(6), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVNO") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(7), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVC") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(8), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVNC") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(9), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVB") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(10), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVBE") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(11), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVA") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(12), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVAE") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(13), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVL") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(14), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVLE") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(15), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVG") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(16), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMOVGE") => Instruction::Binary { op: OPCode::CMOVcc as u8, ext_op: Some(17), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });

        alias!(m: Caseless("CMOVE") => Caseless("CMOVZ"));
        alias!(m: Caseless("CMOVNE") => Caseless("CMOVNZ"));
        alias!(m: Caseless("CMOVPE") => Caseless("CMOVP"));
        alias!(m: Caseless("CMOVPO") => Caseless("CMOVNP"));
        alias!(m: Caseless("CMOVNAE") => Caseless("CMOVB"));
        alias!(m: Caseless("CMOVNA") => Caseless("CMOVBE"));
        alias!(m: Caseless("CMOVNBE") => Caseless("CMOVA"));
        alias!(m: Caseless("CMOVNB") => Caseless("CMOVAE"));
        alias!(m: Caseless("CMOVNGE") => Caseless("CMOVL"));
        alias!(m: Caseless("CMOVNG") => Caseless("CMOVLE"));
        alias!(m: Caseless("CMOVNLE") => Caseless("CMOVG"));
        alias!(m: Caseless("CMOVNL") => Caseless("CMOVGE"));
        
        insert!(m: Caseless("LEA") => Instruction::LEA);
        insert!(m: Caseless("XCHG") => Instruction::BinaryLvalueUnord { op: OPCode::XCHG as u8, ext_op: None, allowed_sizes: STANDARD_SIZES });

        insert!(m: Caseless("SETZ") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(0), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETNZ") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(1), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETS") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(2), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETNS") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(3), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETP") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(4), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETNP") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(5), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETO") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(6), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETNO") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(7), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETC") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(8), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETNC") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(9), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETB") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(10), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETBE") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(11), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETA") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(12), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETAE") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(13), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETL") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(14), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETLE") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(15), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETG") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(16), allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("SETGE") => Instruction::Unary { op: OPCode::SETcc as u8, ext_op: Some(17), allowed_sizes: STANDARD_SIZES });

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

        insert!(m: Caseless("STAC") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(0) });
        insert!(m: Caseless("CLAC") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(1) });
        insert!(m: Caseless("CMAC") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(2) });
        insert!(m: Caseless("STC") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(3) });
        insert!(m: Caseless("CLC") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(4) });
        insert!(m: Caseless("CMC") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(5) });
        insert!(m: Caseless("STD") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(6) });
        insert!(m: Caseless("CLD") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(7) });
        insert!(m: Caseless("CMD") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(8) });
        insert!(m: Caseless("STI") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(9) });
        insert!(m: Caseless("CLI") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(10) });
        insert!(m: Caseless("CMI") => Instruction::NoArg { op: Some(OPCode::REGOP as u8), ext_op: Some(11) });

        insert!(m: Caseless("ADD") => Instruction::Binary { op: OPCode::ADD as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("SUB") => Instruction::Binary { op: OPCode::SUB as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("CMP") => Instruction::CMP);

        insert!(m: Caseless("AND") => Instruction::Binary { op: OPCode::AND as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("OR") => Instruction::Binary { op: OPCode::OR as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("XOR") => Instruction::Binary { op: OPCode::XOR as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("TEST") => Instruction::Binary { op: OPCode::TEST as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });

        insert!(m: Caseless("SHL") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(0), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("SHR") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(1), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("SAR") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(2), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });
        
        insert!(m: Caseless("ROL") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(3), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("ROR") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(4), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("RCL") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(5), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("RCR") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(6), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: Some(Size::Byte), force_b_imm_size: Some(Size::Byte) });

        insert!(m: Caseless("SHLX") => Instruction::Ternary { op: OPCode::BITWISE as u8, ext_op: Some(7), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("SHRX") => Instruction::Ternary { op: OPCode::BITWISE as u8, ext_op: Some(8), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("SARX") => Instruction::Ternary { op: OPCode::BITWISE as u8, ext_op: Some(9), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });

        alias!(m: Caseless("SAL") => Caseless("SHL"));
        alias!(m: Caseless("SALX") => Caseless("SHLX"));

        insert!(m: Caseless("BT") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(10), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("BTC") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(11), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("BTR") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(12), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });
        insert!(m: Caseless("BTS") => Instruction::Binary { op: OPCode::BITWISE as u8, ext_op: Some(13), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: Some(Size::Byte) });

        insert!(m: Caseless("MUL") => Instruction::MUL);
        insert!(m: Caseless("IMUL") => Instruction::IMUL);
        insert!(m: Caseless("MULX") => Instruction::Ternary { op: OPCode::MULDIV as u8, ext_op: Some(3), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });
        insert!(m: Caseless("IMULX") => Instruction::Ternary { op: OPCode::MULDIV as u8, ext_op: Some(7), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, force_b_rm_size: None, force_b_imm_size: None });

        insert!(m: Caseless("DIV") => Instruction::Value { op: OPCode::MULDIV as u8, ext_op: Some(8), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, default_size: None });
        insert!(m: Caseless("IDIV") => Instruction::Value { op: OPCode::MULDIV as u8, ext_op: Some(9), allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, default_size: None });

        insert!(m: Caseless("JMP") => Instruction::Value { op: OPCode::JMP as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });

        insert!(m: Caseless("JZ") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(0), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JNZ") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(1), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JS") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(2), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JNS") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(3), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JP") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(4), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JNP") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(5), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JO") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(6), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JNO") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(7), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JC") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(8), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JNC") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(9), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JB") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(10), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JBE") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(11), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JA") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(12), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JAE") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(13), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JL") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(14), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JLE") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(15), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JG") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(16), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JGE") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(17), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JCXZ") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(18), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JECXZ") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(19), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("JRCXZ") => Instruction::Value { op: OPCode::Jcc as u8, ext_op: Some(20), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });

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

        insert!(m: Caseless("LOOP") => Instruction::Value { op: OPCode::LOOPcc as u8, ext_op: Some(0), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("LOOPZ") => Instruction::Value { op: OPCode::LOOPcc as u8, ext_op: Some(1), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("LOOPNZ") => Instruction::Value { op: OPCode::LOOPcc as u8, ext_op: Some(2), allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });

        alias!(m: Caseless("LOOPE") => Caseless("LOOPZ"));
        alias!(m: Caseless("LOOPNE") => Caseless("LOOPNZ"));

        insert!(m: Caseless("CALL") => Instruction::Value { op: OPCode::CALL as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: NON_BYTE_STANDARD_SIZES, default_size: Some(Size::Qword) });
        insert!(m: Caseless("RET") => Instruction::NoArg { op: Some(OPCode::RET as u8), ext_op: None });

        insert!(m: Caseless("PUSH") => Instruction::Value { op: OPCode::PUSH as u8, ext_op: None, allowed_type: HoleType::Integer, allowed_sizes: STANDARD_SIZES, default_size: None });
        insert!(m: Caseless("POP") => Instruction::Unary { op: OPCode::POP as u8, ext_op: None, allowed_sizes: NON_BYTE_STANDARD_SIZES });

        insert!(m: Caseless("INC") => Instruction::Unary { op: OPCode::INC as u8, ext_op: None, allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("DEC") => Instruction::Unary { op: OPCode::DEC as u8, ext_op: None, allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("NEG") => Instruction::Unary { op: OPCode::NEG as u8, ext_op: None, allowed_sizes: STANDARD_SIZES });
        insert!(m: Caseless("NOT") => Instruction::Unary { op: OPCode::NOT as u8, ext_op: None, allowed_sizes: STANDARD_SIZES });
        
        insert!(m: Caseless("MOVSB") => Instruction::MOVS(Size::Byte));
        insert!(m: Caseless("MOVSW") => Instruction::MOVS(Size::Word));
        insert!(m: Caseless("MOVSD") => Instruction::MOVS(Size::Dword));
        insert!(m: Caseless("MOVSQ") => Instruction::MOVS(Size::Qword));

        insert!(m: Caseless("STOSB") => Instruction::STOS(Size::Byte));
        insert!(m: Caseless("STOSW") => Instruction::STOS(Size::Word));
        insert!(m: Caseless("STOSD") => Instruction::STOS(Size::Dword));
        insert!(m: Caseless("STOSQ") => Instruction::STOS(Size::Qword));

        insert!(m: Caseless("FINIT") => Instruction::NoArg { op: Some(OPCode::FINIT as u8), ext_op: None });

        insert!(m: Caseless("FLD") => Instruction::FPUValue { op: OPCode::FLD as u8, ext_op: None, int: false });
        insert!(m: Caseless("FILD") => Instruction::FPUValue { op: OPCode::FLD as u8, ext_op: None, int: true });

        insert!(m: Caseless("FADD") => Instruction::FPUBinary { op: OPCode::FADD as u8, ext_op: None, int: false, pop: false });
        insert!(m: Caseless("FADDP") => Instruction::FPUBinary { op: OPCode::FADD as u8, ext_op: None, int: false, pop: true });
        insert!(m: Caseless("FIADD") => Instruction::FPUBinary { op: OPCode::FADD as u8, ext_op: None, int: true, pop: false });

        insert!(m: Caseless("FSUB") => Instruction::FPUBinary { op: OPCode::FSUB as u8, ext_op: None, int: false, pop: false });
        insert!(m: Caseless("FSUBP") => Instruction::FPUBinary { op: OPCode::FSUB as u8, ext_op: None, int: false, pop: true });
        insert!(m: Caseless("FISUB") => Instruction::FPUBinary { op: OPCode::FSUB as u8, ext_op: None, int: true, pop: false });

        insert!(m: Caseless("FSUBR") => Instruction::FPUBinary { op: OPCode::FSUBR as u8, ext_op: None, int: false, pop: false });
        insert!(m: Caseless("FSUBRP") => Instruction::FPUBinary { op: OPCode::FSUBR as u8, ext_op: None, int: false, pop: true });
        insert!(m: Caseless("FISUBR") => Instruction::FPUBinary { op: OPCode::FSUBR as u8, ext_op: None, int: true, pop: false });

        insert!(m: Caseless("KMOVB") => Instruction::VPUKMove { size: Size::Byte });
        insert!(m: Caseless("KMOVW") => Instruction::VPUKMove { size: Size::Word });
        insert!(m: Caseless("KMOVD") => Instruction::VPUKMove { size: Size::Dword });
        insert!(m: Caseless("KMOVQ") => Instruction::VPUKMove { size: Size::Qword });

        insert!(m: Caseless("VMOVDQA") => Instruction::VPUMove { elem_size: None, packed: true, aligned: true });
        insert!(m: Caseless("VMOVDQA64") => Instruction::VPUMove { elem_size: Some(Size::Qword), packed: true, aligned: true });
        insert!(m: Caseless("VMOVDQA32") => Instruction::VPUMove { elem_size: Some(Size::Dword), packed: true, aligned: true });
        insert!(m: Caseless("VMOVDQA16") => Instruction::VPUMove { elem_size: Some(Size::Word), packed: true, aligned: true });
        insert!(m: Caseless("VMOVDQA8") => Instruction::VPUMove { elem_size: Some(Size::Byte), packed: true, aligned: true });

        suggest!(m: Caseless("MOVDQA") => [ Caseless("VMOVDQA") ]);
        suggest!(m: Caseless("MOVDQA64") => [ Caseless("VMOVDQA64") ]);
        suggest!(m: Caseless("MOVDQA32") => [ Caseless("VMOVDQA32") ]);
        suggest!(m: Caseless("MOVDQA16") => [ Caseless("VMOVDQA16") ]);
        suggest!(m: Caseless("MOVDQA8") => [ Caseless("VMOVDQA8") ]);

        insert!(m: Caseless("VMOVDQU") => Instruction::VPUMove { elem_size: None, packed: true, aligned: false });
        insert!(m: Caseless("VMOVDQU64") => Instruction::VPUMove { elem_size: Some(Size::Qword), packed: true, aligned: false });
        insert!(m: Caseless("VMOVDQU32") => Instruction::VPUMove { elem_size: Some(Size::Dword), packed: true, aligned: false });
        insert!(m: Caseless("VMOVDQU16") => Instruction::VPUMove { elem_size: Some(Size::Word), packed: true, aligned: false });
        insert!(m: Caseless("VMOVDQU8") => Instruction::VPUMove { elem_size: Some(Size::Byte), packed: true, aligned: false });

        suggest!(m: Caseless("MOVDQU") => [ Caseless("VMOVDQU") ]);
        suggest!(m: Caseless("MOVDQU64") => [ Caseless("VMOVDQU64") ]);
        suggest!(m: Caseless("MOVDQU32") => [ Caseless("VMOVDQU32") ]);
        suggest!(m: Caseless("MOVDQU16") => [ Caseless("VMOVDQU16") ]);
        suggest!(m: Caseless("MOVDQU8") => [ Caseless("VMOVDQU8") ]);

        insert!(m: Caseless("VMOVQ") => Instruction::VPUMove { elem_size: Some(Size::Qword), packed: false, aligned: false });
        insert!(m: Caseless("VMOVD") => Instruction::VPUMove { elem_size: Some(Size::Dword), packed: false, aligned: false });
        insert!(m: Caseless("VMOVW") => Instruction::VPUMove { elem_size: Some(Size::Word), packed: false, aligned: false });
        insert!(m: Caseless("VMOVB") => Instruction::VPUMove { elem_size: Some(Size::Byte), packed: false, aligned: false });

        suggest!(m: Caseless("MOVQ") => [ Caseless("VMOVQ") ]);
        suggest!(m: Caseless("MOVD") => [ Caseless("VMOVD") ]);
        suggest!(m: Caseless("MOVW") => [ Caseless("VMOVW") ]);
        suggest!(m: Caseless("MOVB") => [ Caseless("VMOVB"), Caseless("CMOVB") ]);

        alias!(m: Caseless("VMOVAPD") => Caseless("VMOVDQA64"));
        alias!(m: Caseless("VMOVAPS") => Caseless("VMOVDQA32"));

        alias!(m: Caseless("VMOVUPD") => Caseless("VMOVDQU64"));
        alias!(m: Caseless("VMOVUPS") => Caseless("VMOVDQU32"));

        alias!(m: Caseless("VMOVSD") => Caseless("VMOVQ"));
        alias!(m: Caseless("VMOVSS") => Caseless("VMOVD"));

        insert!(m: Caseless("VADDSD") => Instruction::VPUBinary { op: OPCode::VPUBinary as u8, ext_op: Some(0), elem_size: Size::Qword, packed: false });
        insert!(m: Caseless("VADDPD") => Instruction::VPUBinary { op: OPCode::VPUBinary as u8, ext_op: Some(0), elem_size: Size::Qword, packed: true });
        insert!(m: Caseless("VADDSS") => Instruction::VPUBinary { op: OPCode::VPUBinary as u8, ext_op: Some(1), elem_size: Size::Dword, packed: false });
        insert!(m: Caseless("VADDPS") => Instruction::VPUBinary { op: OPCode::VPUBinary as u8, ext_op: Some(1), elem_size: Size::Dword, packed: true });

        suggest!(m: Caseless("ADDSD") => [ Caseless("VADDSD") ]);
        suggest!(m: Caseless("ADDPD") => [ Caseless("VADDPD") ]);
        suggest!(m: Caseless("ADDSS") => [ Caseless("VADDSS") ]);
        suggest!(m: Caseless("ADDPS") => [ Caseless("VADDPS") ]);

        insert!(m: Caseless("DEBUG_CPU") => Instruction::NoArg { op: Some(OPCode::DEBUG as u8), ext_op: Some(0) });

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
        s.extend(VPU_MASK_REGISTER_INFO.keys().copied());
        s.extend(SEGMENTS.keys().copied());
        s.extend(PREFIXES.keys().copied());
        s.extend(INSTRUCTIONS.keys().copied());

        s
    };
}