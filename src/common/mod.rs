//! Everything that is used by both `asm` and `exec`.

use std::io::{self, Read, Write};

pub mod serialization;
pub mod util;
pub mod f80;

use serialization::*;

/// The supported op codes for the execution engine.
/// 
/// Nearly all of these have sub-encodings and therefore actually encode many more instructions.
#[derive(Clone, Copy, Debug)]
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

pub struct Executable {
    text_seglen: u64,
    rodata_seglen: u64,
    data_seglen: u64,
    bss_seglen: u64,
    content: Vec<u8>,
}
const EXE_PREFIX: &[u8] = "csx64-exe\0".as_bytes();
impl BinaryWrite for Executable {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        EXE_PREFIX.bin_write(f)?;

        self.text_seglen.bin_write(f)?;
        self.rodata_seglen.bin_write(f)?;
        self.data_seglen.bin_write(f)?;
        self.bss_seglen.bin_write(f)?;
        self.content.bin_write(f)
    }
}
impl BinaryRead for Executable {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Executable> {
        if Vec::<u8>::bin_read(f)? != EXE_PREFIX {
            return Err(io::ErrorKind::InvalidData.into());
        }

        let text_seglen = BinaryRead::bin_read(f)?;
        let rodata_seglen = BinaryRead::bin_read(f)?;
        let data_seglen = BinaryRead::bin_read(f)?;
        let bss_seglen = BinaryRead::bin_read(f)?;
        let content = BinaryRead::bin_read(f)?;

        Ok(Executable { text_seglen, rodata_seglen, data_seglen, bss_seglen, content })
    }
}
