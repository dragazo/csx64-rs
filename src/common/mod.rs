//! Everything that is used by both `asm` and `exec`.

use std::io::{self, Read, Write};

pub mod serialization;
pub mod f80;
pub(crate) mod util;

use serialization::*;

/// The supported op codes for the execution engine.
/// 
/// Nearly all of these have sub-encodings and therefore actually encode many more instructions.
#[derive(Clone, Copy, Debug, FromPrimitive)]
#[repr(u8)]
pub enum OPCode
{
    // x86 instructions

    NOP,
    HLT,
    SYSCALL,

    LEA,
    MOV, MOVcc,
    XCHG,

    ADD, SUB,
    AND, OR, XOR,
    CMP, CMPZ, TEST,
    MULDIV,

    JMP, Jcc, LOOPcc, CALL, RET,
    PUSH, POP,

    INC, DEC, NEG, NOT,






    

    

    // SETcc,

    // SHL, SHR, SAL, SAR, ROL, ROR, RCL, RCR,

    // STLDF,
    // FlagManip,

    // BSWAP, BEXTR, BLSI, BLSMSK, BLSR, ANDN, BTx,
    // Cxy, MOVxX,
    // ADXX, AAX,

    // STRING,

    // BSx, TZCNT,

    // UD,

    // IO,

    // // x87 instructions

    // FWAIT,
    // FINIT, FCLEX,
    // FSTLDword,
    // FLDconst, FLD, FST, FXCH, FMOVcc,

    // FADD, FSUB, FSUBR,
    // FMUL, FDIV, FDIVR,

    // F2XM1, FABS, FCHS, FPREM, FPREM1, FRNDINT, FSQRT, FYL2X, FYL2XP1, FXTRACT, FSCALE,
    // FXAM, FTST, FCOM,
    // FSIN, FCOS, FSINCOS, FPTAN, FPATAN,
    // FINCDECSTP, FFREE,

    // // SIMD instructions

    // VPUMOV,

    // VPUFADD, VPUFSUB, VPUFMUL, VPUFDIV,
    // VPUAND, VPUOR, VPUXOR, VPUANDN,
    // VPUADD, VPUADDS, VPUADDUS,
    // VPUSUB, VPUSUBS, VPUSUBUS,
    // VPUMULL,

    // VPUFMIN, VPUFMAX,
    // VPUUMIN, VPUSMIN, VPUUMAX, VPUSMAX,

    // VPUFADDSUB,
    // VPUAVG,

    // VPUFCMP, VPUFCOMI,

    // VPUFSQRT, VPUFRSQRT,

    // VPUCVT,

    // // misc instructions

    // TRANS,

    // DEBUG,
}

/// The system calls recognized by the emulator.
/// 
/// System call codes should be loaded into the `RAX` register.
/// Because 32-bit writes zero the upper 32-bits and syscall codes are unsigned, it suffices to write to `EAX`.
/// Arguments to a system call procedure should be loaded into `RBX`, `RCX`, `RDX` (or partitions thereof, depending on procedure).
#[derive(Clone, Copy, FromPrimitive)]
#[repr(u32)]
pub enum Syscall {
    /// Instructs the emulator to end execution in a non-error state with the `i32` return value in `EBX`.
    /// This effectively means the program terminated rather than crashing.
    Exit,
    Read, Write, Seek,
}

/// An executable file for use by the [`Emulator`].
/// 
/// Executables are produced by [`link`] by combining one or more [`ObjectFile`].
/// 
/// [`Emulator`]: ../exec/struct.Emulator.html
/// [`link`]: ../asm/fn.link.html
/// [`ObjectFile`]: ../asm/struct.ObjectFile.html
pub struct Executable {
    pub(crate) text_seglen: usize,
    pub(crate) rodata_seglen: usize,
    pub(crate) data_seglen: usize,
    pub(crate) bss_seglen: usize,
    pub(crate) content: Vec<u8>,
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
