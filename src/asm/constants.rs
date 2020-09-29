use std::collections::{HashMap, HashSet};

use super::expr::*;
use super::Sizecode;

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
    pub(super) static ref ADDITIONAL_RESERVED_SYMBOLS: HashSet<&'static str> = {
        let mut s = HashSet::new();

        s.insert("BYTE");
        s.insert("WORD");
        s.insert("DWORD");
        s.insert("QWORD");
        s.insert("XMMWORD");
        s.insert("YMMWORD");
        s.insert("ZMMWORD");
        s.insert("OWORD");
        s.insert("TWORD");

        s
    };
}

#[derive(Clone, Copy)]
pub(super) struct CPURegisterInfo {
    pub(super) id: u8,
    pub(super) sizecode: Sizecode,
    pub(super) high: bool,
}
lazy_static! {
    pub(super) static ref CPU_REGISTER_INFO: HashMap<&'static str, CPURegisterInfo> = {
        let mut m = HashMap::new();

        m.insert("RAX", CPURegisterInfo { id: 0, sizecode: Sizecode(3), high: false });
        m.insert("RBX", CPURegisterInfo { id: 1, sizecode: Sizecode(3), high: false });
        m.insert("RCX", CPURegisterInfo { id: 2, sizecode: Sizecode(3), high: false });
        m.insert("RDX", CPURegisterInfo { id: 3, sizecode: Sizecode(3), high: false });
        m.insert("RSI", CPURegisterInfo { id: 4, sizecode: Sizecode(3), high: false });
        m.insert("RDI", CPURegisterInfo { id: 5, sizecode: Sizecode(3), high: false });
        m.insert("RBP", CPURegisterInfo { id: 6, sizecode: Sizecode(3), high: false });
        m.insert("RSP", CPURegisterInfo { id: 7, sizecode: Sizecode(3), high: false });
        m.insert("R8", CPURegisterInfo { id: 8, sizecode: Sizecode(3), high: false });
        m.insert("R9", CPURegisterInfo { id: 9, sizecode: Sizecode(3), high: false });
        m.insert("R10", CPURegisterInfo { id: 10, sizecode: Sizecode(3), high: false });
        m.insert("R11", CPURegisterInfo { id: 11, sizecode: Sizecode(3), high: false });
        m.insert("R12", CPURegisterInfo { id: 12, sizecode: Sizecode(3), high: false });
        m.insert("R13", CPURegisterInfo { id: 13, sizecode: Sizecode(3), high: false });
        m.insert("R14", CPURegisterInfo { id: 14, sizecode: Sizecode(3), high: false });
        m.insert("R15", CPURegisterInfo { id: 15, sizecode: Sizecode(3), high: false });

        m.insert("EAX", CPURegisterInfo { id: 0, sizecode: Sizecode(2), high: false });
        m.insert("EBX", CPURegisterInfo { id: 1, sizecode: Sizecode(2), high: false });
        m.insert("ECX", CPURegisterInfo { id: 2, sizecode: Sizecode(2), high: false });
        m.insert("EDX", CPURegisterInfo { id: 3, sizecode: Sizecode(2), high: false });
        m.insert("ESI", CPURegisterInfo { id: 4, sizecode: Sizecode(2), high: false });
        m.insert("EDI", CPURegisterInfo { id: 5, sizecode: Sizecode(2), high: false });
        m.insert("EBP", CPURegisterInfo { id: 6, sizecode: Sizecode(2), high: false });
        m.insert("ESP", CPURegisterInfo { id: 7, sizecode: Sizecode(2), high: false });
        m.insert("R8D", CPURegisterInfo { id: 8, sizecode: Sizecode(2), high: false });
        m.insert("R9D", CPURegisterInfo { id: 9, sizecode: Sizecode(2), high: false });
        m.insert("R10D", CPURegisterInfo { id: 10, sizecode: Sizecode(2), high: false });
        m.insert("R11D", CPURegisterInfo { id: 11, sizecode: Sizecode(2), high: false });
        m.insert("R12D", CPURegisterInfo { id: 12, sizecode: Sizecode(2), high: false });
        m.insert("R13D", CPURegisterInfo { id: 13, sizecode: Sizecode(2), high: false });
        m.insert("R14D", CPURegisterInfo { id: 14, sizecode: Sizecode(2), high: false });
        m.insert("R15D", CPURegisterInfo { id: 15, sizecode: Sizecode(2), high: false });

        m.insert("AX", CPURegisterInfo { id: 0, sizecode: Sizecode(1), high: false });
        m.insert("BX", CPURegisterInfo { id: 1, sizecode: Sizecode(1), high: false });
        m.insert("CX", CPURegisterInfo { id: 2, sizecode: Sizecode(1), high: false });
        m.insert("DX", CPURegisterInfo { id: 3, sizecode: Sizecode(1), high: false });
        m.insert("SI", CPURegisterInfo { id: 4, sizecode: Sizecode(1), high: false });
        m.insert("DI", CPURegisterInfo { id: 5, sizecode: Sizecode(1), high: false });
        m.insert("BP", CPURegisterInfo { id: 6, sizecode: Sizecode(1), high: false });
        m.insert("SP", CPURegisterInfo { id: 7, sizecode: Sizecode(1), high: false });
        m.insert("R8W", CPURegisterInfo { id: 8, sizecode: Sizecode(1), high: false });
        m.insert("R9W", CPURegisterInfo { id: 9, sizecode: Sizecode(1), high: false });
        m.insert("R10W", CPURegisterInfo { id: 10, sizecode: Sizecode(1), high: false });
        m.insert("R11W", CPURegisterInfo { id: 11, sizecode: Sizecode(1), high: false });
        m.insert("R12W", CPURegisterInfo { id: 12, sizecode: Sizecode(1), high: false });
        m.insert("R13W", CPURegisterInfo { id: 13, sizecode: Sizecode(1), high: false });
        m.insert("R14W", CPURegisterInfo { id: 14, sizecode: Sizecode(1), high: false });
        m.insert("R15W", CPURegisterInfo { id: 15, sizecode: Sizecode(1), high: false });

        m.insert("AL", CPURegisterInfo { id: 0, sizecode: Sizecode(0), high: false });
        m.insert("BL", CPURegisterInfo { id: 1, sizecode: Sizecode(0), high: false });
        m.insert("CL", CPURegisterInfo { id: 2, sizecode: Sizecode(0), high: false });
        m.insert("DL", CPURegisterInfo { id: 3, sizecode: Sizecode(0), high: false });
        m.insert("SIL", CPURegisterInfo { id: 4, sizecode: Sizecode(0), high: false });
        m.insert("DIL", CPURegisterInfo { id: 5, sizecode: Sizecode(0), high: false });
        m.insert("BPL", CPURegisterInfo { id: 6, sizecode: Sizecode(0), high: false });
        m.insert("SPL", CPURegisterInfo { id: 7, sizecode: Sizecode(0), high: false });
        m.insert("R8B", CPURegisterInfo { id: 8, sizecode: Sizecode(0), high: false });
        m.insert("R9B", CPURegisterInfo { id: 9, sizecode: Sizecode(0), high: false });
        m.insert("R10B", CPURegisterInfo { id: 10, sizecode: Sizecode(0), high: false });
        m.insert("R11B", CPURegisterInfo { id: 11, sizecode: Sizecode(0), high: false });
        m.insert("R12B", CPURegisterInfo { id: 12, sizecode: Sizecode(0), high: false });
        m.insert("R13B", CPURegisterInfo { id: 13, sizecode: Sizecode(0), high: false });
        m.insert("R14B", CPURegisterInfo { id: 14, sizecode: Sizecode(0), high: false });
        m.insert("R15B", CPURegisterInfo { id: 15, sizecode: Sizecode(0), high: false });

        m.insert("AH", CPURegisterInfo { id: 0, sizecode: Sizecode(0), high: true });
        m.insert("BH", CPURegisterInfo { id: 1, sizecode: Sizecode(0), high: true });
        m.insert("CH", CPURegisterInfo { id: 2, sizecode: Sizecode(0), high: true });
        m.insert("DH", CPURegisterInfo { id: 3, sizecode: Sizecode(0), high: true });

        m
    };
}

#[derive(Clone, Copy)]
pub(super) struct FPURegisterInfo {
    pub(super) id: u8,
}
lazy_static! {
    pub(super) static ref FPU_REGISTER_INFO: HashMap<&'static str, FPURegisterInfo> = {
        let mut m = HashMap::new();

        m.insert("ST", FPURegisterInfo { id: 0 });

        m.insert("ST0", FPURegisterInfo { id: 0 });
        m.insert("ST1", FPURegisterInfo { id: 1 });
        m.insert("ST2", FPURegisterInfo { id: 2 });
        m.insert("ST3", FPURegisterInfo { id: 3 });
        m.insert("ST4", FPURegisterInfo { id: 4 });
        m.insert("ST5", FPURegisterInfo { id: 5 });
        m.insert("ST6", FPURegisterInfo { id: 6 });
        m.insert("ST7", FPURegisterInfo { id: 7 });

        m
    };
}

#[derive(Clone, Copy)]
pub(super) struct VPURegisterInfo {
    pub(super) id: u8,
    pub(super) sizecode: Sizecode,
}
lazy_static! {
    pub(super) static ref VPU_REGISTER_INFO: HashMap<&'static str, VPURegisterInfo> = {
        let mut m = HashMap::new();

        m.insert("XMM0", VPURegisterInfo { id: 0, sizecode: Sizecode(4) });
        m.insert("XMM1", VPURegisterInfo { id: 1, sizecode: Sizecode(4) });
        m.insert("XMM2", VPURegisterInfo { id: 2, sizecode: Sizecode(4) });
        m.insert("XMM3", VPURegisterInfo { id: 3, sizecode: Sizecode(4) });
        m.insert("XMM4", VPURegisterInfo { id: 4, sizecode: Sizecode(4) });
        m.insert("XMM5", VPURegisterInfo { id: 5, sizecode: Sizecode(4) });
        m.insert("XMM6", VPURegisterInfo { id: 6, sizecode: Sizecode(4) });
        m.insert("XMM7", VPURegisterInfo { id: 7, sizecode: Sizecode(4) });
        m.insert("XMM8", VPURegisterInfo { id: 8, sizecode: Sizecode(4) });
        m.insert("XMM9", VPURegisterInfo { id: 9, sizecode: Sizecode(4) });
        m.insert("XMM10", VPURegisterInfo { id: 10, sizecode: Sizecode(4) });
        m.insert("XMM11", VPURegisterInfo { id: 11, sizecode: Sizecode(4) });
        m.insert("XMM12", VPURegisterInfo { id: 12, sizecode: Sizecode(4) });
        m.insert("XMM13", VPURegisterInfo { id: 13, sizecode: Sizecode(4) });
        m.insert("XMM14", VPURegisterInfo { id: 14, sizecode: Sizecode(4) });
        m.insert("XMM15", VPURegisterInfo { id: 15, sizecode: Sizecode(4) });

        m.insert("YMM0", VPURegisterInfo { id: 0, sizecode: Sizecode(5) });
        m.insert("YMM1", VPURegisterInfo { id: 1, sizecode: Sizecode(5) });
        m.insert("YMM2", VPURegisterInfo { id: 2, sizecode: Sizecode(5) });
        m.insert("YMM3", VPURegisterInfo { id: 3, sizecode: Sizecode(5) });
        m.insert("YMM4", VPURegisterInfo { id: 4, sizecode: Sizecode(5) });
        m.insert("YMM5", VPURegisterInfo { id: 5, sizecode: Sizecode(5) });
        m.insert("YMM6", VPURegisterInfo { id: 6, sizecode: Sizecode(5) });
        m.insert("YMM7", VPURegisterInfo { id: 7, sizecode: Sizecode(5) });
        m.insert("YMM8", VPURegisterInfo { id: 8, sizecode: Sizecode(5) });
        m.insert("YMM9", VPURegisterInfo { id: 9, sizecode: Sizecode(5) });
        m.insert("YMM10", VPURegisterInfo { id: 10, sizecode: Sizecode(5) });
        m.insert("YMM11", VPURegisterInfo { id: 11, sizecode: Sizecode(5) });
        m.insert("YMM12", VPURegisterInfo { id: 12, sizecode: Sizecode(5) });
        m.insert("YMM13", VPURegisterInfo { id: 13, sizecode: Sizecode(5) });
        m.insert("YMM14", VPURegisterInfo { id: 14, sizecode: Sizecode(5) });
        m.insert("YMM15", VPURegisterInfo { id: 15, sizecode: Sizecode(5) });

        m.insert("ZMM0", VPURegisterInfo { id: 0, sizecode: Sizecode(6) });
        m.insert("ZMM1", VPURegisterInfo { id: 1, sizecode: Sizecode(6) });
        m.insert("ZMM2", VPURegisterInfo { id: 2, sizecode: Sizecode(6) });
        m.insert("ZMM3", VPURegisterInfo { id: 3, sizecode: Sizecode(6) });
        m.insert("ZMM4", VPURegisterInfo { id: 4, sizecode: Sizecode(6) });
        m.insert("ZMM5", VPURegisterInfo { id: 5, sizecode: Sizecode(6) });
        m.insert("ZMM6", VPURegisterInfo { id: 6, sizecode: Sizecode(6) });
        m.insert("ZMM7", VPURegisterInfo { id: 7, sizecode: Sizecode(6) });
        m.insert("ZMM8", VPURegisterInfo { id: 8, sizecode: Sizecode(6) });
        m.insert("ZMM9", VPURegisterInfo { id: 9, sizecode: Sizecode(6) });
        m.insert("ZMM10", VPURegisterInfo { id: 10, sizecode: Sizecode(6) });
        m.insert("ZMM11", VPURegisterInfo { id: 11, sizecode: Sizecode(6) });
        m.insert("ZMM12", VPURegisterInfo { id: 12, sizecode: Sizecode(6) });
        m.insert("ZMM13", VPURegisterInfo { id: 13, sizecode: Sizecode(6) });
        m.insert("ZMM14", VPURegisterInfo { id: 14, sizecode: Sizecode(6) });
        m.insert("ZMM15", VPURegisterInfo { id: 15, sizecode: Sizecode(6) });
        m.insert("ZMM16", VPURegisterInfo { id: 16, sizecode: Sizecode(6) });
        m.insert("ZMM17", VPURegisterInfo { id: 17, sizecode: Sizecode(6) });
        m.insert("ZMM18", VPURegisterInfo { id: 18, sizecode: Sizecode(6) });
        m.insert("ZMM19", VPURegisterInfo { id: 19, sizecode: Sizecode(6) });
        m.insert("ZMM20", VPURegisterInfo { id: 20, sizecode: Sizecode(6) });
        m.insert("ZMM21", VPURegisterInfo { id: 21, sizecode: Sizecode(6) });
        m.insert("ZMM22", VPURegisterInfo { id: 22, sizecode: Sizecode(6) });
        m.insert("ZMM23", VPURegisterInfo { id: 23, sizecode: Sizecode(6) });
        m.insert("ZMM24", VPURegisterInfo { id: 24, sizecode: Sizecode(6) });
        m.insert("ZMM25", VPURegisterInfo { id: 25, sizecode: Sizecode(6) });
        m.insert("ZMM26", VPURegisterInfo { id: 26, sizecode: Sizecode(6) });
        m.insert("ZMM27", VPURegisterInfo { id: 27, sizecode: Sizecode(6) });
        m.insert("ZMM28", VPURegisterInfo { id: 28, sizecode: Sizecode(6) });
        m.insert("ZMM29", VPURegisterInfo { id: 29, sizecode: Sizecode(6) });
        m.insert("ZMM30", VPURegisterInfo { id: 30, sizecode: Sizecode(6) });
        m.insert("ZMM31", VPURegisterInfo { id: 31, sizecode: Sizecode(6) });

        m
    };
}

lazy_static! {
    static ref VALID_LOCK_INSTRUCTIONS: HashSet<&'static str> = {
        let mut s = HashSet::new();

        s.insert("ADD");
        s.insert("ADC");
        s.insert("AND");
        s.insert("BTC");
        s.insert("BTR");
        s.insert("BTS");
        s.insert("CMPXCHG");
        s.insert("CMPXCHG8B");
        s.insert("CMPXCHG16B");
        s.insert("DEC");
        s.insert("INC");
        s.insert("NEG");
        s.insert("NOT");
        s.insert("OR");
        s.insert("SBB");
        s.insert("SUB");
        s.insert("XOR");
        s.insert("XADD");
        s.insert("XCHG");

        s
    };
}
