use std::collections::{HashMap, BTreeMap, BTreeSet};

use super::expr::*;
use super::Size;
use super::caseless::Caseless;

bitflags! {
    pub(super) struct AsmSegment: u8 {
        const TEXT = 1;
        const RODATA = 2;
        const DATA = 4;
        const BSS = 8;
    }
}

pub(super) const COMMENT_CHAR: char = ';';
pub(super) const LABEL_DEF_CHAR: char = ':';

pub(super) const CURRENT_LINE_MACRO: &str = "$";
pub(super) const START_OF_SEG_MACRO: &str = "$$";
pub(super) const TIMES_ITER_MACRO: &str = "$I";

pub(super) const POINTER_MACRO: &str = "$PTR";

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
        
        m.insert(OP::Mul, (5, Associativity::Left));

        m.insert(OP::Div, (5, Associativity::Left));
        m.insert(OP::Mod, (5, Associativity::Left));

        m.insert(OP::Add, (6, Associativity::Left));
        m.insert(OP::Sub, (6, Associativity::Left));

        m.insert(OP::SHL, (7, Associativity::Left));
        m.insert(OP::SHR, (7, Associativity::Left));

        m.insert(OP::Less, (9, Associativity::Left));
        m.insert(OP::LessE, (9, Associativity::Left));
        m.insert(OP::Great, (9, Associativity::Left));
        m.insert(OP::GreatE, (9, Associativity::Left));

        m.insert(OP::Equ, (10, Associativity::Left));
        m.insert(OP::Neq, (10, Associativity::Left));

        m.insert(OP::And, (11, Associativity::Left));
        m.insert(OP::Xor, (12, Associativity::Left));
        m.insert(OP::Or, (13, Associativity::Left));

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

lazy_static! {
    pub(super) static ref SEG_OFFSETS: HashMap<AsmSegment, &'static str> = {
        let mut m = HashMap::new();

        m.insert(AsmSegment::TEXT, "#t");
        m.insert(AsmSegment::RODATA, "#r");
        m.insert(AsmSegment::DATA, "#d");
        m.insert(AsmSegment::BSS, "#b");

        m
    };
}

lazy_static! {
    pub(super) static ref SEG_ORIGINS: HashMap<AsmSegment, &'static str> = {
        let mut m = HashMap::new();

        m.insert(AsmSegment::TEXT, "#T");
        m.insert(AsmSegment::RODATA, "#R");
        m.insert(AsmSegment::DATA, "#D");
        m.insert(AsmSegment::BSS, "#B");

        m
    };
}
pub(super) const BINARY_LITERAL_SYMBOL_PREFIX: &str = "#L";

pub(super) const PTRDIFF_IDS: &[&'static str] = &["#t", "#r", "#d", "#b", "#T", "#R", "#D", "#B"];

lazy_static! {
    pub(super) static ref ADDITIONAL_RESERVED_SYMBOLS: BTreeSet<Caseless<'static>> = {
        let mut s = BTreeSet::new();

        s.insert(Caseless("BYTE"));
        s.insert(Caseless("WORD"));
        s.insert(Caseless("DWORD"));
        s.insert(Caseless("QWORD"));
        s.insert(Caseless("XMMWORD"));
        s.insert(Caseless("YMMWORD"));
        s.insert(Caseless("ZMMWORD"));
        s.insert(Caseless("TWORD"));

        s
    };
}

lazy_static! {
    pub(super) static ref SIZE_KEYWORDS: BTreeMap<Caseless<'static>, Size> = {
        let mut m = BTreeMap::new();

        m.insert(Caseless("BYTE"), Size::Byte);
        m.insert(Caseless("WORD"), Size::Word);
        m.insert(Caseless("DWORD"), Size::Dword);
        m.insert(Caseless("QWORD"), Size::Qword);
        m.insert(Caseless("XMMWORD"), Size::Xmmword);
        m.insert(Caseless("YMMWORD"), Size::Ymmword);
        m.insert(Caseless("ZMMWORD"), Size::Zmmword);
        m.insert(Caseless("TWORD"), Size::Tword);

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

        m.insert(Caseless("RAX"), CPURegisterInfo { id: 0, size: Size::Qword, high: false });
        m.insert(Caseless("RBX"), CPURegisterInfo { id: 1, size: Size::Qword, high: false });
        m.insert(Caseless("RCX"), CPURegisterInfo { id: 2, size: Size::Qword, high: false });
        m.insert(Caseless("RDX"), CPURegisterInfo { id: 3, size: Size::Qword, high: false });
        m.insert(Caseless("RSI"), CPURegisterInfo { id: 4, size: Size::Qword, high: false });
        m.insert(Caseless("RDI"), CPURegisterInfo { id: 5, size: Size::Qword, high: false });
        m.insert(Caseless("RBP"), CPURegisterInfo { id: 6, size: Size::Qword, high: false });
        m.insert(Caseless("RSP"), CPURegisterInfo { id: 7, size: Size::Qword, high: false });
        m.insert(Caseless("R8"), CPURegisterInfo { id: 8, size: Size::Qword, high: false });
        m.insert(Caseless("R9"), CPURegisterInfo { id: 9, size: Size::Qword, high: false });
        m.insert(Caseless("R10"), CPURegisterInfo { id: 10, size: Size::Qword, high: false });
        m.insert(Caseless("R11"), CPURegisterInfo { id: 11, size: Size::Qword, high: false });
        m.insert(Caseless("R12"), CPURegisterInfo { id: 12, size: Size::Qword, high: false });
        m.insert(Caseless("R13"), CPURegisterInfo { id: 13, size: Size::Qword, high: false });
        m.insert(Caseless("R14"), CPURegisterInfo { id: 14, size: Size::Qword, high: false });
        m.insert(Caseless("R15"), CPURegisterInfo { id: 15, size: Size::Qword, high: false });

        m.insert(Caseless("EAX"), CPURegisterInfo { id: 0, size: Size::Dword, high: false });
        m.insert(Caseless("EBX"), CPURegisterInfo { id: 1, size: Size::Dword, high: false });
        m.insert(Caseless("ECX"), CPURegisterInfo { id: 2, size: Size::Dword, high: false });
        m.insert(Caseless("EDX"), CPURegisterInfo { id: 3, size: Size::Dword, high: false });
        m.insert(Caseless("ESI"), CPURegisterInfo { id: 4, size: Size::Dword, high: false });
        m.insert(Caseless("EDI"), CPURegisterInfo { id: 5, size: Size::Dword, high: false });
        m.insert(Caseless("EBP"), CPURegisterInfo { id: 6, size: Size::Dword, high: false });
        m.insert(Caseless("ESP"), CPURegisterInfo { id: 7, size: Size::Dword, high: false });
        m.insert(Caseless("R8D"), CPURegisterInfo { id: 8, size: Size::Dword, high: false });
        m.insert(Caseless("R9D"), CPURegisterInfo { id: 9, size: Size::Dword, high: false });
        m.insert(Caseless("R10D"), CPURegisterInfo { id: 10, size: Size::Dword, high: false });
        m.insert(Caseless("R11D"), CPURegisterInfo { id: 11, size: Size::Dword, high: false });
        m.insert(Caseless("R12D"), CPURegisterInfo { id: 12, size: Size::Dword, high: false });
        m.insert(Caseless("R13D"), CPURegisterInfo { id: 13, size: Size::Dword, high: false });
        m.insert(Caseless("R14D"), CPURegisterInfo { id: 14, size: Size::Dword, high: false });
        m.insert(Caseless("R15D"), CPURegisterInfo { id: 15, size: Size::Dword, high: false });

        m.insert(Caseless("AX"), CPURegisterInfo { id: 0, size: Size::Word, high: false });
        m.insert(Caseless("BX"), CPURegisterInfo { id: 1, size: Size::Word, high: false });
        m.insert(Caseless("CX"), CPURegisterInfo { id: 2, size: Size::Word, high: false });
        m.insert(Caseless("DX"), CPURegisterInfo { id: 3, size: Size::Word, high: false });
        m.insert(Caseless("SI"), CPURegisterInfo { id: 4, size: Size::Word, high: false });
        m.insert(Caseless("DI"), CPURegisterInfo { id: 5, size: Size::Word, high: false });
        m.insert(Caseless("BP"), CPURegisterInfo { id: 6, size: Size::Word, high: false });
        m.insert(Caseless("SP"), CPURegisterInfo { id: 7, size: Size::Word, high: false });
        m.insert(Caseless("R8W"), CPURegisterInfo { id: 8, size: Size::Word, high: false });
        m.insert(Caseless("R9W"), CPURegisterInfo { id: 9, size: Size::Word, high: false });
        m.insert(Caseless("R10W"), CPURegisterInfo { id: 10, size: Size::Word, high: false });
        m.insert(Caseless("R11W"), CPURegisterInfo { id: 11, size: Size::Word, high: false });
        m.insert(Caseless("R12W"), CPURegisterInfo { id: 12, size: Size::Word, high: false });
        m.insert(Caseless("R13W"), CPURegisterInfo { id: 13, size: Size::Word, high: false });
        m.insert(Caseless("R14W"), CPURegisterInfo { id: 14, size: Size::Word, high: false });
        m.insert(Caseless("R15W"), CPURegisterInfo { id: 15, size: Size::Word, high: false });

        m.insert(Caseless("AL"), CPURegisterInfo { id: 0, size: Size::Byte, high: false });
        m.insert(Caseless("BL"), CPURegisterInfo { id: 1, size: Size::Byte, high: false });
        m.insert(Caseless("CL"), CPURegisterInfo { id: 2, size: Size::Byte, high: false });
        m.insert(Caseless("DL"), CPURegisterInfo { id: 3, size: Size::Byte, high: false });
        m.insert(Caseless("SIL"), CPURegisterInfo { id: 4, size: Size::Byte, high: false });
        m.insert(Caseless("DIL"), CPURegisterInfo { id: 5, size: Size::Byte, high: false });
        m.insert(Caseless("BPL"), CPURegisterInfo { id: 6, size: Size::Byte, high: false });
        m.insert(Caseless("SPL"), CPURegisterInfo { id: 7, size: Size::Byte, high: false });
        m.insert(Caseless("R8B"), CPURegisterInfo { id: 8, size: Size::Byte, high: false });
        m.insert(Caseless("R9B"), CPURegisterInfo { id: 9, size: Size::Byte, high: false });
        m.insert(Caseless("R10B"), CPURegisterInfo { id: 10, size: Size::Byte, high: false });
        m.insert(Caseless("R11B"), CPURegisterInfo { id: 11, size: Size::Byte, high: false });
        m.insert(Caseless("R12B"), CPURegisterInfo { id: 12, size: Size::Byte, high: false });
        m.insert(Caseless("R13B"), CPURegisterInfo { id: 13, size: Size::Byte, high: false });
        m.insert(Caseless("R14B"), CPURegisterInfo { id: 14, size: Size::Byte, high: false });
        m.insert(Caseless("R15B"), CPURegisterInfo { id: 15, size: Size::Byte, high: false });

        m.insert(Caseless("AH"), CPURegisterInfo { id: 0, size: Size::Byte, high: true });
        m.insert(Caseless("BH"), CPURegisterInfo { id: 1, size: Size::Byte, high: true });
        m.insert(Caseless("CH"), CPURegisterInfo { id: 2, size: Size::Byte, high: true });
        m.insert(Caseless("DH"), CPURegisterInfo { id: 3, size: Size::Byte, high: true });

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

        m.insert(Caseless("ST"), FPURegisterInfo { id: 0 });

        m.insert(Caseless("ST0"), FPURegisterInfo { id: 0 });
        m.insert(Caseless("ST1"), FPURegisterInfo { id: 1 });
        m.insert(Caseless("ST2"), FPURegisterInfo { id: 2 });
        m.insert(Caseless("ST3"), FPURegisterInfo { id: 3 });
        m.insert(Caseless("ST4"), FPURegisterInfo { id: 4 });
        m.insert(Caseless("ST5"), FPURegisterInfo { id: 5 });
        m.insert(Caseless("ST6"), FPURegisterInfo { id: 6 });
        m.insert(Caseless("ST7"), FPURegisterInfo { id: 7 });

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

        m.insert(Caseless("XMM0"), VPURegisterInfo { id: 0, size: Size::Xmmword });
        m.insert(Caseless("XMM1"), VPURegisterInfo { id: 1, size: Size::Xmmword });
        m.insert(Caseless("XMM2"), VPURegisterInfo { id: 2, size: Size::Xmmword });
        m.insert(Caseless("XMM3"), VPURegisterInfo { id: 3, size: Size::Xmmword });
        m.insert(Caseless("XMM4"), VPURegisterInfo { id: 4, size: Size::Xmmword });
        m.insert(Caseless("XMM5"), VPURegisterInfo { id: 5, size: Size::Xmmword });
        m.insert(Caseless("XMM6"), VPURegisterInfo { id: 6, size: Size::Xmmword });
        m.insert(Caseless("XMM7"), VPURegisterInfo { id: 7, size: Size::Xmmword });
        m.insert(Caseless("XMM8"), VPURegisterInfo { id: 8, size: Size::Xmmword });
        m.insert(Caseless("XMM9"), VPURegisterInfo { id: 9, size: Size::Xmmword });
        m.insert(Caseless("XMM10"), VPURegisterInfo { id: 10, size: Size::Xmmword });
        m.insert(Caseless("XMM11"), VPURegisterInfo { id: 11, size: Size::Xmmword });
        m.insert(Caseless("XMM12"), VPURegisterInfo { id: 12, size: Size::Xmmword });
        m.insert(Caseless("XMM13"), VPURegisterInfo { id: 13, size: Size::Xmmword });
        m.insert(Caseless("XMM14"), VPURegisterInfo { id: 14, size: Size::Xmmword });
        m.insert(Caseless("XMM15"), VPURegisterInfo { id: 15, size: Size::Xmmword });

        m.insert(Caseless("YMM0"), VPURegisterInfo { id: 0, size: Size::Ymmword });
        m.insert(Caseless("YMM1"), VPURegisterInfo { id: 1, size: Size::Ymmword });
        m.insert(Caseless("YMM2"), VPURegisterInfo { id: 2, size: Size::Ymmword });
        m.insert(Caseless("YMM3"), VPURegisterInfo { id: 3, size: Size::Ymmword });
        m.insert(Caseless("YMM4"), VPURegisterInfo { id: 4, size: Size::Ymmword });
        m.insert(Caseless("YMM5"), VPURegisterInfo { id: 5, size: Size::Ymmword });
        m.insert(Caseless("YMM6"), VPURegisterInfo { id: 6, size: Size::Ymmword });
        m.insert(Caseless("YMM7"), VPURegisterInfo { id: 7, size: Size::Ymmword });
        m.insert(Caseless("YMM8"), VPURegisterInfo { id: 8, size: Size::Ymmword });
        m.insert(Caseless("YMM9"), VPURegisterInfo { id: 9, size: Size::Ymmword });
        m.insert(Caseless("YMM10"), VPURegisterInfo { id: 10, size: Size::Ymmword });
        m.insert(Caseless("YMM11"), VPURegisterInfo { id: 11, size: Size::Ymmword });
        m.insert(Caseless("YMM12"), VPURegisterInfo { id: 12, size: Size::Ymmword });
        m.insert(Caseless("YMM13"), VPURegisterInfo { id: 13, size: Size::Ymmword });
        m.insert(Caseless("YMM14"), VPURegisterInfo { id: 14, size: Size::Ymmword });
        m.insert(Caseless("YMM15"), VPURegisterInfo { id: 15, size: Size::Ymmword });

        m.insert(Caseless("ZMM0"), VPURegisterInfo { id: 0, size: Size::Zmmword });
        m.insert(Caseless("ZMM1"), VPURegisterInfo { id: 1, size: Size::Zmmword });
        m.insert(Caseless("ZMM2"), VPURegisterInfo { id: 2, size: Size::Zmmword });
        m.insert(Caseless("ZMM3"), VPURegisterInfo { id: 3, size: Size::Zmmword });
        m.insert(Caseless("ZMM4"), VPURegisterInfo { id: 4, size: Size::Zmmword });
        m.insert(Caseless("ZMM5"), VPURegisterInfo { id: 5, size: Size::Zmmword });
        m.insert(Caseless("ZMM6"), VPURegisterInfo { id: 6, size: Size::Zmmword });
        m.insert(Caseless("ZMM7"), VPURegisterInfo { id: 7, size: Size::Zmmword });
        m.insert(Caseless("ZMM8"), VPURegisterInfo { id: 8, size: Size::Zmmword });
        m.insert(Caseless("ZMM9"), VPURegisterInfo { id: 9, size: Size::Zmmword });
        m.insert(Caseless("ZMM10"), VPURegisterInfo { id: 10, size: Size::Zmmword });
        m.insert(Caseless("ZMM11"), VPURegisterInfo { id: 11, size: Size::Zmmword });
        m.insert(Caseless("ZMM12"), VPURegisterInfo { id: 12, size: Size::Zmmword });
        m.insert(Caseless("ZMM13"), VPURegisterInfo { id: 13, size: Size::Zmmword });
        m.insert(Caseless("ZMM14"), VPURegisterInfo { id: 14, size: Size::Zmmword });
        m.insert(Caseless("ZMM15"), VPURegisterInfo { id: 15, size: Size::Zmmword });
        m.insert(Caseless("ZMM16"), VPURegisterInfo { id: 16, size: Size::Zmmword });
        m.insert(Caseless("ZMM17"), VPURegisterInfo { id: 17, size: Size::Zmmword });
        m.insert(Caseless("ZMM18"), VPURegisterInfo { id: 18, size: Size::Zmmword });
        m.insert(Caseless("ZMM19"), VPURegisterInfo { id: 19, size: Size::Zmmword });
        m.insert(Caseless("ZMM20"), VPURegisterInfo { id: 20, size: Size::Zmmword });
        m.insert(Caseless("ZMM21"), VPURegisterInfo { id: 21, size: Size::Zmmword });
        m.insert(Caseless("ZMM22"), VPURegisterInfo { id: 22, size: Size::Zmmword });
        m.insert(Caseless("ZMM23"), VPURegisterInfo { id: 23, size: Size::Zmmword });
        m.insert(Caseless("ZMM24"), VPURegisterInfo { id: 24, size: Size::Zmmword });
        m.insert(Caseless("ZMM25"), VPURegisterInfo { id: 25, size: Size::Zmmword });
        m.insert(Caseless("ZMM26"), VPURegisterInfo { id: 26, size: Size::Zmmword });
        m.insert(Caseless("ZMM27"), VPURegisterInfo { id: 27, size: Size::Zmmword });
        m.insert(Caseless("ZMM28"), VPURegisterInfo { id: 28, size: Size::Zmmword });
        m.insert(Caseless("ZMM29"), VPURegisterInfo { id: 29, size: Size::Zmmword });
        m.insert(Caseless("ZMM30"), VPURegisterInfo { id: 30, size: Size::Zmmword });
        m.insert(Caseless("ZMM31"), VPURegisterInfo { id: 31, size: Size::Zmmword });

        m
    };
}

lazy_static! {
    static ref VALID_LOCK_INSTRUCTIONS: BTreeSet<Caseless<'static>> = {
        let mut s = BTreeSet::new();

        s.insert(Caseless("ADD"));
        s.insert(Caseless("ADC"));
        s.insert(Caseless("AND"));
        s.insert(Caseless("BTC"));
        s.insert(Caseless("BTR"));
        s.insert(Caseless("BTS"));
        s.insert(Caseless("CMPXCHG"));
        s.insert(Caseless("CMPXCHG8B"));
        s.insert(Caseless("CMPXCHG16B"));
        s.insert(Caseless("DEC"));
        s.insert(Caseless("INC"));
        s.insert(Caseless("NEG"));
        s.insert(Caseless("NOT"));
        s.insert(Caseless("OR"));
        s.insert(Caseless("SBB"));
        s.insert(Caseless("SUB"));
        s.insert(Caseless("XOR"));
        s.insert(Caseless("XADD"));
        s.insert(Caseless("XCHG"));

        s
    };
}
