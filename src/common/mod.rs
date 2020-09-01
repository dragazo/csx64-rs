//! Everything that is used by both `asm` and `exec`.

pub mod serialization;

/// The supported op codes for the execution engine.
/// 
/// Nearly all of these have sub-encodings and therefore actually encode many more instructions.
#[derive(Clone, Copy)]
#[repr(u8)]
pub enum OPCode
{
    // x86 instructions

    NOP,
    HLT, SYSCALL,
    STLDF,
    FlagManip,

    SETcc, MOV, MOVcc, XCHG,

    JMP, Jcc, LOOPcc, CALL, RET,
    PUSH, POP,
    LEA,

    ADD, SUB,
    MULx, IMUL, DIV, IDIV,
    SHL, SHR, SAL, SAR, ROL, ROR, RCL, RCR,
    AND, OR, XOR,
    INC, DEC, NEG, NOT,

    CMP, CMPZ, TEST,

    BSWAP, BEXTR, BLSI, BLSMSK, BLSR, ANDN, BTx,
    Cxy, MOVxX,
    ADXX, AAX,

    STRING,

    BSx, TZCNT,

    UD,

    IO,

    // x87 instructions

    FWAIT,
    FINIT, FCLEX,
    FSTLDword,
    FLDconst, FLD, FST, FXCH, FMOVcc,

    FADD, FSUB, FSUBR,
    FMUL, FDIV, FDIVR,

    F2XM1, FABS, FCHS, FPREM, FPREM1, FRNDINT, FSQRT, FYL2X, FYL2XP1, FXTRACT, FSCALE,
    FXAM, FTST, FCOM,
    FSIN, FCOS, FSINCOS, FPTAN, FPATAN,
    FINCDECSTP, FFREE,

    // SIMD instructions

    VPUMOV,

    VPUFADD, VPUFSUB, VPUFMUL, VPUFDIV,
    VPUAND, VPUOR, VPUXOR, VPUANDN,
    VPUADD, VPUADDS, VPUADDUS,
    VPUSUB, VPUSUBS, VPUSUBUS,
    VPUMULL,

    VPUFMIN, VPUFMAX,
    VPUUMIN, VPUSMIN, VPUUMAX, VPUSMAX,

    VPUFADDSUB,
    VPUAVG,

    VPUFCMP, VPUFCOMI,

    VPUFSQRT, VPUFRSQRT,

    VPUCVT,

    // misc instructions

    TRANS,

    DEBUG = 255,
}
