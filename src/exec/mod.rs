//! Everything pertaining to executing CSX64 executables.

use rand_xorshift::XorShiftRng;
use rand::{Rng, RngCore, SeedableRng, rngs::OsRng};
use memchr::memchr;
use num_traits::FromPrimitive;

use std::mem;
use std::iter;
use std::sync::{Arc, Mutex};

use crate::common::util::*;
use crate::common::f80::*;
use crate::common::{OPCode, Executable, Syscall};

pub mod registers;
pub mod fpu;
pub mod fs;

use registers::*;
use fpu::*;
use fs::*;

/// Bitmask denoting Flags that users can modify with instructions like POPF.
pub const MODIFIABLE_FLAGS: u64 = 0x003f0fd5;

/// Default max on emulator main memory footprint.
pub const DEFAULT_MAX_MEM: usize = 2 * 1024 * 1024 * 1024;
/// Default stack size to provide an emulator.
pub const DEFAULT_STACK_SIZE: usize = 2 * 1024 * 1024;
/// Default number of file descriptors.
pub const DEFAULT_MAX_FD: usize = 16;

/// Current state of an emulator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    /// The emulator has not been initialized with a program to run.
    Uninitialized,
    /// The emulator is still running.
    Running,
    /// The emulator terminated successfully with the given return code.
    Terminated(i32),
    /// The emulator terminated due to an error.
    Error(ExecError),
}

/// Reasons why an error can happen during execution.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExecError {
    /// A load or store was outside the range of allocated memory.
    MemOutOfBounds,
    /// A stack operation overflowed into program space.
    StackOverflow,
    /// A stack operation underflowed into heap space.
    StackUnderflow,
    /// A store was performed in readonly memory (e.g. text or rodata segments).
    WriteInReadonlyMemory,
    /// The instruction pointer was inside non-executable memory.
    ExecuteNonExecutableMemory,
    /// An operation encoding was invalid.
    /// This should be impossible if the assembler/linker were used to create the executable,
    /// unless the user wrote content to the text segment manually.
    InvalidOpEncoding,
    /// An opcode was not recognized.
    /// Much like `InvalidOpEncoding`, this is impossible with proper usage of the assembler/linker.
    UnrecognizedOpCode,
    /// A division instruction attempted to divide by zero.
    DivideByZero,
    /// An extended division instruction had a quotient which could not be truncated to the normal size.
    DivisionOverflow,
    /// When a system call was invoked, the requested procedure was not recognized.
    UnrecognizedSyscall,
    /// An illegal file descriptor was provided to an IO system call.
    FileDescriptorOutOfBounds,
    /// Attempt to perform an IO system call on a file descriptor which was not open.
    FileDescriptorNotOpen,
    /// Attempt to violate established file permissions.
    FilePermissions,
}

/// Reason why execution stopped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StopReason {
    /// Emulator was not in the running state.
    NotRunning,
    /// Emulator executed the requested number of cycles.
    MaxCycles,
    /// Emulated program requested to forfeit the remainder of its execution timeslot.
    /// This can be done explicitly by the `HTL` instruction or implicitly from a blocking operation.
    ForfeitTimeslot,
    /// An error was encountered during execution.
    /// For convenience, this variant stores the error,
    /// but it can also be accessed by testing the emulator state.
    Error(ExecError),
    /// The program successfully terminated.
    /// For convenince, this variant stores the return code,
    /// but it can also be accessed by testing the emulator state.
    Terminated(i32),
}

/// Truncates a value to the given size, which is then zero extended to 64-bit.
fn truncate(val: u64, sizecode: u8) -> u64 {
    match sizecode {
        0 => val as u8 as u64,
        1 => val as u16 as u64,
        2 => val as u32 as u64,
        3 => val,
        _ => panic!(),
    }
}
/// Sign extends a value of the given initial size to 64-bit.
/// The conversion is first performed by truncation, so bits outside the specified size range are ignored.
fn sign_extend(val: u64, sizecode: u8) -> u64 {
    match sizecode {
        0 => val as i8 as u64,
        1 => val as i16 as u64,
        2 => val as i32 as u64,
        3 => val,
        _ => panic!(),
    }
}
/// Gets the sign bit of the value with given size.
/// Bits outside the range of the size are ignored.
fn sign_bit(val: u64, sizecode: u8) -> bool {
    match sizecode {
        0 => (val as i8) < 0,
        1 => (val as i16) < 0,
        2 => (val as i32) < 0,
        3 => (val as i64) < 0,
        _ => panic!(),
    }
}
/// Checks if the value has even parity.
fn is_parity_even(val: u8) -> bool {
    val.count_ones() % 2 == 0
}

macro_rules! calc_mul {
    ($a:ident, $b:ident : $normal:ty, $extended:ty, $normal_bits:literal) => {{
        let full = $a as $normal as $extended * $b as $normal as $extended;
        ((full >> $normal_bits) as u64, full as u64, full as $normal as $extended != full)
    }}
}

/// Computes the unsigned product of `a` and `b`, split into high and low halves.
/// Bits in `a` and `b` that are outside of `sizecode` are ignored.
/// For the low half of the result, bits outside the range of `sizecode` but up to `sizecode+1` are the truncated full value.
/// For the upper half, bits outside the range of `sizecode` are undefined.
/// Also returns a flag denoting if the operation overflowed `sizecode`.
fn raw_mul(sizecode: u8, a: u64, b: u64) -> (u64, u64, bool) {
    match sizecode {
        0 => calc_mul!(a, b : u8, u16, 8),
        1 => calc_mul!(a, b : u16, u32, 16),
        2 => calc_mul!(a, b : u32, u64, 32),
        3 => calc_mul!(a, b : u64, u128, 64),
        _ => unreachable!(),
    }
}
/// As `raw_mul` except performs signed multiplication.
fn raw_imul(sizecode: u8, a: u64, b: u64) -> (u64, u64, bool) {
    match sizecode {
        0 => calc_mul!(a, b : i8, i16, 8),
        1 => calc_mul!(a, b : i16, i32, 16),
        2 => calc_mul!(a, b : i32, i64, 32),
        3 => calc_mul!(a, b : i64, i128, 64),
        _ => unreachable!(),
    }
}

macro_rules! calc_div {
    ($a:ident, $b:ident : $normal:ty, $extended:ty) => {{
        let (quo, rem) = quotient_and_remainder($a as $extended, $b as $normal as $extended);
        (quo as u64, rem as u64, quo as $normal as $extended != quo)
    }}
}

/// Computes the division of the extended numerator `a` by the denominator `b`.
/// Returns the low half of the quotient, the remainder, and a flag denoting overflow of the quotient.
/// Bits outside the range of sizecode+1 (for a), or sizecode (for b) are ignored.
/// Bits outside the range of sizecode for both results are undefined.
fn raw_div(sizecode: u8, a: u128, b: u64) -> (u64, u64, bool) {
    match sizecode {
        0 => calc_div!(a, b : u8, u16),
        1 => calc_div!(a, b : u16, u32),
        2 => calc_div!(a, b : u32, u64),
        3 => calc_div!(a, b : u64, u128),
        _ => unreachable!(),
    }
}
fn raw_idiv(sizecode: u8, a: u128, b: u64) -> (u64, u64, bool) {
    match sizecode {
        0 => calc_div!(a, b : i8, i16),
        1 => calc_div!(a, b : i16, i32),
        2 => calc_div!(a, b : i32, i64),
        3 => calc_div!(a, b : i64, i128),
        _ => unreachable!(),
    }
}

macro_rules! impl_mem_primitive {
    ($([ $get:ident, $set:ident => $t:ty ]),*$(,)?) => {$(
        pub fn $get(&self, pos: u64) -> Result<$t, ExecError> {
            let mut v = [0; mem::size_of::<$t>()];
            v.copy_from_slice(self.get(pos, mem::size_of::<$t>() as u64)?);
            Ok(<$t>::from_le_bytes(v))
        }
        pub fn $set(&mut self, pos: u64, val: $t) -> Result<(), ExecError> {
            self.set(pos, &val.to_le_bytes())
        }
    )*}
}
macro_rules! impl_stack_primitive {
    ($([ $push:ident, $pop:ident => $t:ty ]),*$(,)?) => {$(
        pub fn $push(&mut self, val: $t) -> Result<(), ExecError> {
            self.push_mem(&val.to_le_bytes())
        }
        pub fn $pop(&mut self) -> Result<$t, ExecError> {
            let mut v = [0; mem::size_of::<$t>()];
            v.copy_from_slice(self.pop_mem(mem::size_of::<$t>() as u64)?);
            Ok(<$t>::from_le_bytes(v))
        }
    )*}
}
macro_rules! impl_mem_adv_primitive {
    ($([ $get_adv:ident : $t:ty => $f:ident  ]),*$(,)?) => {$(
        fn $get_adv(&mut self) -> Result<$t, ExecError> {
            let res = self.memory.$f(self.instruction_pointer as u64)?;
            self.instruction_pointer += mem::size_of::<$t>(); // success of read implies this won't overflow
            Ok(res)
        }
    )*}
}

macro_rules! impl_string_repeat {
    ($self:ident, $sizecode:ident, $func:ident, $cond:expr) => {{
        let mut rcx;
        if $self.flags.get_ots() {
            while { rcx = $self.cpu.get_rcx(); rcx != 0 } {
                $func($self, $sizecode)?;
                $self.cpu.set_rcx(rcx - 1);
                if !$cond { break }
            }
        } else if {rcx = $self.cpu.get_rcx(); rcx != 0 } {
            $func($self, $sizecode)?;
            $self.cpu.set_rcx(rcx - 1);
            if $cond { $self.instruction_pointer -= 2; }
        }
        Ok(())
    }}
}

/// Holds options for initializing an emulator.
#[derive(Default)]
pub struct EmulatorArgs {
    /// Maximum amount of memory the emulator can provide to the program.
    /// If omitted, defaults to `DEFAULT_MAX_MEM`.
    pub max_memory: Option<usize>,
    /// Amount of stack space to give the program.
    /// If omitted, defaults to `DEFAULT_STACK_SIZE`.
    pub stack_size: Option<usize>,
    /// Max number of file descriptors the program can use at the same time.
    /// If omitted, defaults to `DEFAULT_MAX_FD`.
    pub max_files: Option<usize>,
    /// The command line arguments to provide the program.
    /// This can be left empty, which is the default,
    /// but many programs expect at least one command line argument (typically, exe command).
    pub command_line_args: Vec<String>,
}

/// The memory module of an emulator.
#[derive(Default)]
pub struct Memory {
    raw: Vec<u8>,
    min: usize, // so users can't accidentally truncate the executable itself
    max: usize,

    exe_barrier: usize,      // barrier before which memory is executable
    readonly_barrier: usize, // barrier before which memory is read-only (>= exe_barrier)
    stack_top: usize,        // barrier between program and stack (stack crossing is stack overflow)
    stack_base: usize,       // the base of the stack (high address) (stack crossing is stack underflow)
}
impl Memory {
    /// Gets the length of the currently allocated block of memory.
    pub fn len(&self) -> usize {
        self.raw.len()
    }
    /// Grabs a contiguous block of memory.
    /// Fails if the block goes out of bounds.
    pub fn get(&self, pos: u64, len: u64) -> Result<&[u8], ExecError> {
        if pos > usize::MAX as u64 || len > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let (pos, len) = (pos as usize, len as usize);

        match self.raw.get(pos..pos.wrapping_add(len)) {
            None => Err(ExecError::MemOutOfBounds),
            Some(bin) => Ok(bin),
        }
    }
    /// Similar to `get` but returns a mutable slice.
    /// Additionally, fails if grabbing from readonly memory.
    pub fn get_mut(&mut self, pos: u64, len: u64) -> Result<&mut [u8], ExecError> {
        if pos > usize::MAX as u64 || len > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let (pos, len) = (pos as usize, len as usize);

        if pos < self.readonly_barrier { return Err(ExecError::WriteInReadonlyMemory); }
        match self.raw.get_mut(pos..pos.wrapping_add(len)) {
            None => Err(ExecError::MemOutOfBounds),
            Some(bin) => Ok(bin),
        }
    }
    /// Assigns a binary value to memory.
    /// Equivalent to assigning to the result of `get_mut`.
    /// On failure, the internal state is unmodified.
    pub fn set(&mut self, pos: u64, value: &[u8]) -> Result<(), ExecError> {
        Ok(self.get_mut(pos, value.len() as u64)?.copy_from_slice(value))
    }
    /// Reads a null-terminated binary string starting at the given position.
    /// The null terminator is not included in the result.
    /// If pos itself is a null terminator, returns an empty slice.
    /// Fails if no null terminator is found or the range goes out of bounds.
    pub fn get_null_terminated(&self, pos: u64) -> Result<&[u8], ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let pos = pos as usize;

        if pos >= self.raw.len() { return Err(ExecError::MemOutOfBounds); }
        match memchr(0, &self.raw[pos..]) {
            None => Err(ExecError::MemOutOfBounds),
            Some(stop) => Ok(&self.raw[pos..pos + stop]),
        }
    }
    /// Writes a null-terminated binary string to the given position.
    /// Note that the value need not be null terminated: we simply append a terminator in the internal representation.
    /// Indeed, zeros in the value are included verbatim, though they will not be present with the matching read function.
    /// Fails if the result goes out of bounds or intersects readonly memory.
    /// On failure, the internal state is unmodified.
    pub fn set_null_terminated(&mut self, pos: u64, value: &[u8]) -> Result<(), ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let pos = pos as usize;

        if pos < self.readonly_barrier { return Err(ExecError::WriteInReadonlyMemory); }
        let stop = pos.wrapping_add(value.len());
        if stop >= self.raw.len() { return Err(ExecError::MemOutOfBounds); } // make sure we can boop a terminator on the end
        match self.raw.get_mut(pos..stop) {
            None => return Err(ExecError::MemOutOfBounds), // this also handles overflow of stop sum
            Some(dest) => {
                dest.copy_from_slice(value);
                self.raw[stop] = 0;
                Ok(())
            }
        }
    }

    impl_mem_primitive! {
        [ get_u8,  set_u8  => u8 ],
        [ get_u16, set_u16 => u16 ],
        [ get_u32, set_u32 => u32 ],
        [ get_u64, set_u64 => u64 ],

        [ get_i8,  set_i8  => i8 ],
        [ get_i16, set_i16 => i16 ],
        [ get_i32, set_i32 => i32 ],
        [ get_i64, set_i64 => i64 ],

        [ get_f32, set_f32 => f32 ],
        [ get_f64, set_f64 => f64 ],
        [ get_f80, set_f80 => F80 ],
    }
}

macro_rules! register_aliases {
    ($src:ident => $([ $idx:ident : $t:ty => $get:ident : $getf:ident , $set:ident : $setf:ident ]),*$(,)?) => {$(
        pub fn $get(&self) -> $t {
            self.$src[Self::$idx].$getf()
        }
        pub fn $set(&mut self, val: $t) {
            self.$src[Self::$idx].$setf(val)
        }
    )*}
}

/// The core CPU components of an emulator.
#[derive(Default)]
pub struct CPU {
    pub regs: [CPURegister; 16],
}
impl CPU {
    pub const RAX: usize =  0;
    pub const RBX: usize =  1;
    pub const RCX: usize =  2;
    pub const RDX: usize =  3;
    pub const RSI: usize =  4;
    pub const RDI: usize =  5;
    pub const RBP: usize =  6;
    pub const RSP: usize =  7;
    pub const R8:  usize =  8;
    pub const R9:  usize =  9;
    pub const R10: usize = 10;
    pub const R11: usize = 11;
    pub const R12: usize = 12;
    pub const R13: usize = 13;
    pub const R14: usize = 14;
    pub const R15: usize = 15;

    register_aliases! { regs => 
        [ RAX:u64 => get_rax:get_x64, set_rax:set_x64 ],
        [ RBX:u64 => get_rbx:get_x64, set_rbx:set_x64 ],
        [ RCX:u64 => get_rcx:get_x64, set_rcx:set_x64 ],
        [ RDX:u64 => get_rdx:get_x64, set_rdx:set_x64 ],
        [ RSI:u64 => get_rsi:get_x64, set_rsi:set_x64 ],
        [ RDI:u64 => get_rdi:get_x64, set_rdi:set_x64 ],
        [ RBP:u64 => get_rbp:get_x64, set_rbp:set_x64 ],
        [ RSP:u64 => get_rsp:get_x64, set_rsp:set_x64 ],
        [  R8:u64 => get_r8:get_x64,  set_r8:set_x64 ],
        [  R9:u64 => get_r9:get_x64,  set_r9:set_x64 ],
        [ R10:u64 => get_r10:get_x64, set_r10:set_x64 ],
        [ R11:u64 => get_r11:get_x64, set_r11:set_x64 ],
        [ R12:u64 => get_r12:get_x64, set_r12:set_x64 ],
        [ R13:u64 => get_r13:get_x64, set_r13:set_x64 ],
        [ R14:u64 => get_r14:get_x64, set_r14:set_x64 ],
        [ R15:u64 => get_r15:get_x64, set_r15:set_x64 ],
    
        [ RAX:u32 => get_eax:get_x32,  set_eax:set_x32 ],
        [ RBX:u32 => get_ebx:get_x32,  set_ebx:set_x32 ],
        [ RCX:u32 => get_ecx:get_x32,  set_ecx:set_x32 ],
        [ RDX:u32 => get_edx:get_x32,  set_edx:set_x32 ],
        [ RSI:u32 => get_esi:get_x32,  set_esi:set_x32 ],
        [ RDI:u32 => get_edi:get_x32,  set_edi:set_x32 ],
        [ RBP:u32 => get_ebp:get_x32,  set_ebp:set_x32 ],
        [ RSP:u32 => get_esp:get_x32,  set_esp:set_x32 ],
        [  R8:u32 => get_r8d:get_x32,  set_r8d:set_x32 ],
        [  R9:u32 => get_r9d:get_x32,  set_r9d:set_x32 ],
        [ R10:u32 => get_r10d:get_x32, set_r10d:set_x32 ],
        [ R11:u32 => get_r11d:get_x32, set_r11d:set_x32 ],
        [ R12:u32 => get_r12d:get_x32, set_r12d:set_x32 ],
        [ R13:u32 => get_r13d:get_x32, set_r13d:set_x32 ],
        [ R14:u32 => get_r14d:get_x32, set_r14d:set_x32 ],
        [ R15:u32 => get_r15d:get_x32, set_r15d:set_x32 ],
    
        [ RAX:u16 => get_ax:get_x16,   set_ax:set_x16 ],
        [ RBX:u16 => get_bx:get_x16,   set_bx:set_x16 ],
        [ RCX:u16 => get_cx:get_x16,   set_cx:set_x16 ],
        [ RDX:u16 => get_dx:get_x16,   set_dx:set_x16 ],
        [ RSI:u16 => get_si:get_x16,   set_si:set_x16 ],
        [ RDI:u16 => get_di:get_x16,   set_di:set_x16 ],
        [ RBP:u16 => get_bp:get_x16,   set_bp:set_x16 ],
        [ RSP:u16 => get_sp:get_x16,   set_sp:set_x16 ],
        [  R8:u16 => get_r8w:get_x16,  set_r8w:set_x16 ],
        [  R9:u16 => get_r9w:get_x16,  set_r9w:set_x16 ],
        [ R10:u16 => get_r10w:get_x16, set_r10w:set_x16 ],
        [ R11:u16 => get_r11w:get_x16, set_r11w:set_x16 ],
        [ R12:u16 => get_r12w:get_x16, set_r12w:set_x16 ],
        [ R13:u16 => get_r13w:get_x16, set_r13w:set_x16 ],
        [ R14:u16 => get_r14w:get_x16, set_r14w:set_x16 ],
        [ R15:u16 => get_r15w:get_x16, set_r15w:set_x16 ],
    
        [ RAX:u8 => get_al:get_x8,   set_al:set_x8 ],
        [ RBX:u8 => get_bl:get_x8,   set_bl:set_x8 ],
        [ RCX:u8 => get_cl:get_x8,   set_cl:set_x8 ],
        [ RDX:u8 => get_dl:get_x8,   set_dl:set_x8 ],
        [ RSI:u8 => get_sil:get_x8,  set_sil:set_x8 ],
        [ RDI:u8 => get_dil:get_x8,  set_dil:set_x8 ],
        [ RBP:u8 => get_bpl:get_x8,  set_bpl:set_x8 ],
        [ RSP:u8 => get_spl:get_x8,  set_spl:set_x8 ],
        [  R8:u8 => get_r8b:get_x8,  set_r8b:set_x8 ],
        [  R9:u8 => get_r9b:get_x8,  set_r9b:set_x8 ],
        [ R10:u8 => get_r10b:get_x8, set_r10b:set_x8 ],
        [ R11:u8 => get_r11b:get_x8, set_r11b:set_x8 ],
        [ R12:u8 => get_r12b:get_x8, set_r12b:set_x8 ],
        [ R13:u8 => get_r13b:get_x8, set_r13b:set_x8 ],
        [ R14:u8 => get_r14b:get_x8, set_r14b:set_x8 ],
        [ R15:u8 => get_r15b:get_x8, set_r15b:set_x8 ],
    
        [ RAX:u8 => get_ah:get_x8h, set_ah:set_x8h ],
        [ RBX:u8 => get_bh:get_x8h, set_bh:set_x8h ],
        [ RCX:u8 => get_ch:get_x8h, set_ch:set_x8h ],
        [ RDX:u8 => get_dh:get_x8h, set_dh:set_x8h ],
    }
}

/// The core VPU components of an emulator.
#[derive(Default)]
pub struct VPU {
    pub regs: [ZMMRegister; 32],
    pub mxcsr: MXCSR,
}

/// The opened file handles of the client.
#[derive(Default)]
pub struct Files {
    pub handles: Vec<Option<Arc<Mutex<dyn FileHandle>>>>,
}
impl Files {

}

/// Processor emulator which runs a compiled program.
pub struct Emulator {
    pub memory: Memory,
    pub cpu: CPU,
    pub vpu: VPU,
    pub fpu: FPU,
    pub flags: Flags,
    pub files: Files,

    instruction_pointer: usize,
    state: State,

    rng: XorShiftRng,
}
impl Emulator {
    /// Creates a new emulator in the uninitialized state.
    pub fn new() -> Emulator {
        Emulator {
            memory: Default::default(),
            cpu: Default::default(),
            vpu: Default::default(),
            fpu: Default::default(),
            flags: Default::default(),
            files: Default::default(),

            instruction_pointer: 0,
            state: State::Uninitialized,

            rng: XorShiftRng::from_rng(OsRng).unwrap(),
        }
    }

    /// Initializes the emulator to run the provided executable.
    /// `stack_size`, if provided, specifies the amount of stack memory to provide; if this is `None` then `DEFAULT_STACK_SIZE` is used.
    /// `args` denotes the command line arguments to provide to the program.
    /// These will be copied into the emulator's memory as null-terminated binary arrays (presumably C-style strings) for it to access.
    /// 
    /// Note: as a safety precaution, this function also clears all privileged flags from the flags register.
    /// This includes disabling filesystem syscalls, among other things.
    /// If these features are needed, they must be set enabled again after initialization is completed.
    /// To avoid errors in the emulated program, this should be done prior to running the program and ideally not be revoked mid-execution.
    pub fn init(&mut self, exe: &Executable, args: &EmulatorArgs) {
        let stack_size = args.stack_size.unwrap_or(DEFAULT_STACK_SIZE);

        self.memory.raw.clear(); // discard whatever we had in memory
        self.memory.raw.extend_from_slice(&exe.content); // copy over the exe content (text, rodata, and data segments)
        self.memory.raw.extend(iter::once(0).cycle().take(exe.bss_seglen)); // add the bss segment (0 initialized)
        self.memory.stack_top = self.memory.len(); // this marks the top of the stack
        self.reallocate_random(self.memory.len() + stack_size); // allocate the stack space (random simulates undefined content)
        self.memory.stack_base = self.memory.len(); // this marks the base of the stack

        self.memory.exe_barrier = exe.text_seglen; // compute memory privilege barriers
        self.memory.readonly_barrier = exe.text_seglen + exe.rodata_seglen;

        // compute arg info - start with room for argc (i32), argv (ptr), and an array of (args+1) ptrs (null terminated)
        let mut args_pos = self.memory.stack_base + 4 + 8 + (args.command_line_args.len() + 1) * 8; 
        let mut arg_positions = vec![];
        for arg in args.command_line_args.iter() { // compute target locations and required memory
            arg_positions.push(args_pos);
            args_pos += arg.len() + 1;
        }
        
        // now that we have arg info, allocate and copy content
        self.memory.raw.extend(iter::once(0).cycle().take(args_pos - self.memory.stack_base));
        let argc = arg_positions.len() as u32;
        let argv = self.memory.stack_base as u64 + 4 + 8; // points to the array we're about to create
        self.memory.set_u32(self.memory.stack_base as u64, argc).unwrap();
        self.memory.set_u64(self.memory.stack_base as u64 + 4, argv).unwrap();
        for (i, &pos) in arg_positions.iter().enumerate() {
            self.memory.set_u64(argv + 8 * i as u64, pos as u64).unwrap(); // array of pointers to strings
        }
        self.memory.set_u64(argv + 8 * arg_positions.len() as u64, 0).unwrap(); // null terminate the ptr array (C convention)
        for (i, arg) in args.command_line_args.iter().enumerate() {
            self.memory.set_null_terminated(arg_positions[i] as u64, arg.as_bytes()).unwrap(); // finally, append all the strings
        }

        self.memory.min = self.memory.len(); // current amount of memory is the minimum (so user can't accidentally truncate anything imporant)
        self.memory.max = args.max_memory.unwrap_or(DEFAULT_MAX_MEM);

        // randomize register contents to simulate undefined content
        for reg in self.cpu.regs.iter_mut() {
            reg.0 = self.rng.gen();
        }
        for reg in self.vpu.regs.iter_mut() {
            self.rng.fill_bytes(&mut reg.0);
        }

        // but these registers have a well defined initial state
        self.fpu.reset();
        self.vpu.mxcsr.0 = 0x1f80;
        self.flags.0 = 2;
        self.cpu.set_edi(argc);
        self.cpu.set_rsi(argv);
        self.cpu.set_rsp(self.memory.stack_base as u64);
        self.cpu.set_rbp(self.memory.len() as u64);

        // set up the files - clear anything we had and set capacity (all empty)
        self.files.handles.clear();
        for _ in 0..args.max_files.unwrap_or(DEFAULT_MAX_FD) {
            self.files.handles.push(None); 
        }

        // finally, prepare for execution
        self.instruction_pointer = 0;
        self.state = State::Running;
    }

    /// Reallocates the main memory array to the provided size.
    /// If less than the current size, this truncates the array.
    /// If greater than the current size, fills with random bytes.
    /// Same size is no-op.
    fn reallocate_random(&mut self, new_size: usize) {
        let old_size = self.memory.len();
        if new_size < old_size {
            self.memory.raw.truncate(new_size);
            return;
        }

        self.memory.raw.extend(iter::once(0).cycle().take(new_size - old_size));
        self.rng.fill_bytes(&mut self.memory.raw[old_size..]);
    }

    /// Gets the current state of the emulator.
    pub fn get_state(&self) -> State {
        self.state
    }

    /// Resumes execution of the emulator for up to the given number of cycles.
    /// Returns the number of cycles executed and the reason for stopping.
    pub fn execute_cycles(&mut self, cycles: u64) -> (u64, StopReason) {
        if self.state != State::Running { return (0, StopReason::NotRunning); }

        macro_rules! error_state {
            ($self:ident => $err:expr) => {{
                let e = $err;
                $self.state = State::Error(e);
                StopReason::Error(e)
            }}
        }
        macro_rules! terminated_state {
            ($self:ident => $ret:expr) => {{
                let r = $ret;
                $self.state = State::Terminated(r);
                StopReason::Terminated(r)
            }}
        }

        for cycle in 0..cycles {
            if self.instruction_pointer >= self.memory.exe_barrier {
                return (cycle, error_state!(self => ExecError::ExecuteNonExecutableMemory));
            }
            let res = match self.get_mem_adv_u8() {
                Err(e) => return (cycle, error_state!(self => e)),
                Ok(op) => match OPCode::from_u8(op) {
                    None => return (cycle, error_state!(self => ExecError::UnrecognizedOpCode)),
                    Some(op) => match op {
                        OPCode::NOP => Ok(()),
                        OPCode::HLT => return (cycle + 1, StopReason::ForfeitTimeslot), // +1 because this cycle succeeded
                        OPCode::SYSCALL => match Syscall::from_u64(self.cpu.get_rax()) {
                            None => return (cycle, error_state!(self => ExecError::UnrecognizedSyscall)),
                            Some(proc) => match proc {
                                Syscall::Exit => return (cycle + 1, terminated_state!(self => self.cpu.get_ebx() as i32)), // +1 because this cycle succeeded
                                
                                Syscall::Read => self.exec_sys_read(),
                                Syscall::Write => self.exec_sys_write(),
                                Syscall::Seek => unimplemented!(),

                                Syscall::Break => self.exec_sys_brk(),
                            }
                        }

                        OPCode::LEA => self.exec_lea(),
                        OPCode::MOV => self.exec_mov(),
                        OPCode::MOVcc => self.exec_movcc(),
                        OPCode::SETcc => self.exec_setcc(),
                        OPCode::XCHG => self.exec_xchg(),
                        OPCode::REGOP => self.exec_regop(),

                        OPCode::AND => self.exec_and_helper(true),
                        OPCode::OR => self.exec_or(),
                        OPCode::XOR => self.exec_xor(),
                        OPCode::TEST => self.exec_and_helper(false),
                        OPCode::BITWISE => self.exec_bitwise(),

                        OPCode::ADD => self.exec_add(),
                        OPCode::SUB => self.exec_sub_helper(true),
                        OPCode::CMP => self.exec_sub_helper(false),
                        OPCode::CMPZ => self.exec_cmp0(),

                        OPCode::MULDIV => self.exec_muldiv_family(),

                        OPCode::JMP => self.exec_jmp(),
                        OPCode::Jcc => self.exec_jcc(),
                        OPCode::LOOPcc => self.exec_loopcc(),
                        OPCode::CALL => self.exec_call(),
                        OPCode::RET => self.exec_ret(),

                        OPCode::PUSH => self.exec_push(),
                        OPCode::POP => self.exec_pop(),

                        OPCode::INC => self.exec_inc(),
                        OPCode::DEC => self.exec_dec(),
                        OPCode::NEG => self.exec_neg(),
                        OPCode::NOT => self.exec_not(),

                        OPCode::STRING => self.exec_string(),
                        
                        OPCode::DEBUG => self.exec_debug(),
                    }
                }
            };
            if let Err(e) = res { return (cycle, error_state!(self => e)); }
        }

        (cycles, StopReason::MaxCycles)
    }

    fn jump_to(&mut self, pos: u64) -> Result<(), ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        self.instruction_pointer = pos as usize;
        Ok(())
    }

    // -------------------------------------------------------------------------------------

    /// Pushes a binary value onto the stack.
    /// Similar to using `set_mem` except that it also checks for stack overflow.
    /// On failur, the internal state is unmodified.
    pub fn push_mem(&mut self, value: &[u8]) -> Result<(), ExecError> {
        let pos = self.cpu.get_rsp().wrapping_sub(value.len() as u64);
        if pos < self.memory.stack_top as u64 { return Err(ExecError::StackOverflow); }
        self.memory.set(pos, value)?;
        self.cpu.set_rsp(pos);
        Ok(())
    }
    /// Pops a binary value from the stack.
    /// Returns a reference to the (logically) removed block of memory.
    pub fn pop_mem(&mut self, len: u64) -> Result<&[u8], ExecError> {
        let pos = self.cpu.get_rsp();
        let next_pos = pos.wrapping_add(len);
        if next_pos > self.memory.stack_base as u64 { return Err(ExecError::StackUnderflow); }
        let res = self.memory.get(pos, len)?;
        self.cpu.set_rsp(next_pos);
        Ok(res)
    }

    impl_stack_primitive! {
        [ push_mem_u8,  pop_mem_u8   => u8 ],
        [ push_mem_u16, pop_mem_u16  => u16 ],
        [ push_mem_u32, pop_mem_u32  => u32 ],
        [ push_mem_u64, pop_mem_u64  => u64 ],

        [ push_mem_i8 , pop_mem_i8   => i8 ],
        [ push_mem_i16, pop_mem_i16  => i16 ],
        [ push_mem_i32, pop_mem_i32  => i32 ],
        [ push_mem_i64, pop_mem_i64  => i64 ],

        [ push_mem_f32, pop_mem_f32 => f32 ],
        [ push_mem_f64, pop_mem_f64 => f64 ],
        [ push_mem_f80, pop_mem_f80 => F80 ],
    }

    // -------------------------------------------------------------------------------------

    /// Reads a value from the given position.
    /// Result is zero extended to 64-bit.
    fn raw_get_mem(&self, pos: u64, sizecode: u8) -> Result<u64, ExecError> {
        Ok(match sizecode {
            0 => self.memory.get_u8(pos)? as u64,
            1 => self.memory.get_u16(pos)? as u64,
            2 => self.memory.get_u32(pos)? as u64,
            3 => self.memory.get_u64(pos)?,
            _ => panic!(),
        })
    }
    /// Writes a value to the given position.
    /// If the value is too large, it is truncated.
    fn raw_set_mem(&mut self, pos: u64, sizecode: u8, val: u64) -> Result<(), ExecError> {
        match sizecode {
            0 => self.memory.set_u8(pos, val as u8),
            1 => self.memory.set_u16(pos, val as u16),
            2 => self.memory.set_u32(pos, val as u32),
            3 => self.memory.set_u64(pos, val),
            _ => panic!(),
        }
    }
    /// Pushes a value onto the stack.
    /// If the value is too large, it is truncated.
    fn raw_push_mem(&mut self, sizecode: u8, value: u64) -> Result<(), ExecError> {
        match sizecode {
            0 => self.push_mem_u8(value as u8),
            1 => self.push_mem_u16(value as u16),
            2 => self.push_mem_u32(value as u32),
            3 => self.push_mem_u64(value),
            _ => panic!(),
        }
    }
    /// Pops a value off the stack.
    /// Result is zero extended to 64-bit.
    fn raw_pop_mem(&mut self, sizecode: u8) -> Result<u64, ExecError> {
        Ok(match sizecode {
            0 => self.pop_mem_u8()? as u64,
            1 => self.pop_mem_u16()? as u64,
            2 => self.pop_mem_u32()? as u64,
            3 => self.pop_mem_u64()?,
            _ => panic!(),
        })
    }

    // -------------------------------------------------------------------------------------

    impl_mem_adv_primitive! {
        [ get_mem_adv_u8  :  u8 => get_u8 ],
        [ get_mem_adv_u16 : u16 => get_u16 ],
        [ get_mem_adv_u32 : u32 => get_u32 ],
        [ get_mem_adv_u64 : u64 => get_u64 ],
    }

    /// Simultaneously advances and reads a value at the current instruction pointer position.
    /// The value is zero extended to 64-bit.
    fn raw_get_mem_adv(&mut self, sizecode: u8) -> Result<u64, ExecError> {
        let res = self.raw_get_mem(self.instruction_pointer as u64, sizecode)?;
        self.instruction_pointer += 1 << sizecode;
        Ok(res)
    }

    /// Advances and reads an address format from the current instruction pointer position.
    fn get_address_adv(&mut self) -> Result<u64, ExecError> {
        // [1: imm][1:][2: mult_1][2: size][1: r1][1: r2]   ([4: r1][4: r2])   ([size: imm])

        let settings = self.get_mem_adv_u8()?;
        let regs = if settings & 3 != 0 { self.get_mem_adv_u8()? } else { 0 };
        let sizecode = (settings >> 2) & 3;

        let mut res = if settings & 0x80 != 0 { self.raw_get_mem_adv(sizecode)? } else { 0 };
        if settings & 2 != 0 { res = res.wrapping_add(self.cpu.regs[regs as usize >> 4].raw_get(sizecode) << ((settings >> 4) & 3)); }
        if settings & 1 != 0 { res = res.wrapping_add(self.cpu.regs[regs as usize & 15].raw_get(sizecode)); }

        Ok(truncate(res, sizecode)) // make sure result is same size
    }

    // -------------------------------------------------------------------------------------
    
    fn exec_sys_read(&mut self) -> Result<(), ExecError> {
        let fd = self.cpu.get_rbx();
        if fd > usize::MAX as u64 { return Err(ExecError::FileDescriptorOutOfBounds); }
        let fd = fd as usize;
        if fd > self.files.handles.len() { return Err(ExecError::FileDescriptorOutOfBounds); }

        let count = match &self.files.handles[fd] {
            None => return Err(ExecError::FileDescriptorNotOpen),
            Some(handle) => match handle.lock().unwrap().read(self.memory.get_mut(self.cpu.get_rcx(), self.cpu.get_rdx())?) {
                Ok(n) => n as u64,
                Err(FileError::Permissions) => return Err(ExecError::FilePermissions),
                Err(FileError::IOError(_)) => u64::MAX, // failure simply returns -1 to client
            }
        };
        self.cpu.set_rax(count);
        Ok(())
    }
    fn exec_sys_write(&mut self) -> Result<(), ExecError> {
        let fd = self.cpu.get_rbx();
        if fd > usize::MAX as u64 { return Err(ExecError::FileDescriptorOutOfBounds); }
        let fd = fd as usize;
        if fd > self.files.handles.len() { return Err(ExecError::FileDescriptorOutOfBounds); }

        let count = match &self.files.handles[fd] {
            None => return Err(ExecError::FileDescriptorNotOpen),
            Some(handle) => match handle.lock().unwrap().write_all(self.memory.get(self.cpu.get_rcx(), self.cpu.get_rdx())?) {
                Ok(()) => self.cpu.get_rdx(),
                Err(FileError::Permissions) => return Err(ExecError::FilePermissions),
                Err(FileError::IOError(_)) => u64::MAX, // io failure simply returns -1 to client
            }
        };
        self.cpu.set_rax(count);
        Ok(())
    }

    fn exec_sys_brk(&mut self) -> Result<(), ExecError> {
        let pos = self.cpu.get_rbx();
        if pos == 0 {
            self.cpu.set_rax(self.memory.len() as u64);
            return Ok(());
        }
        if pos > usize::MAX as u64 {
            self.cpu.set_rax(!0);
            return Ok(());
        }
        let pos = pos as usize;
        if pos < self.memory.min || pos > self.memory.max {
            self.cpu.set_rax(!0);
            return Ok(());
        }
        self.reallocate_random(pos);
        debug_assert_eq!(self.memory.len(), pos);
        self.cpu.set_rax(0);
        Ok(())
    }

    // -------------------------------------------------------------------------------------

    /*
    [4: r1][3:][1: r1h]   [binary a b]
    f(r1, a, b)
    */
    fn read_ternary_op(&mut self, get_a: bool, force_b_rm_sizecode: Option<u8>, force_b_imm_sizecode: Option<u8>) -> Result<(u8, u8, u8, u64, u64, u64), ExecError> {
        let s1 = self.get_mem_adv_u8()?;
        let (s2, s3, m, a, b) = self.read_binary_op(get_a, force_b_rm_sizecode, force_b_imm_sizecode)?;
        Ok((s1, s2, s3, m, a, b))
    }
    fn store_ternary_op_result(&mut self, s1: u8, s2: u8, s3: u8, m: u64, res1: u64, res2: Option<u64>) -> Result<(), ExecError> {
        let sizecode = (s2 >> 2) & 3;
        if let Some(res2) = res2 { self.store_binary_op_result(s2, s3, m, res2)? }
        if s1 & 1 != 0 { self.cpu.regs[s1 as usize >> 4].set_x8h(res1 as u8); } else { self.cpu.regs[s1 as usize >> 4].raw_set(sizecode, res1); }
        Ok(())
    }

    /*
    [4: dest][2: size][1:dh][1: sh]   [4: mode][4: src]
    mode = 0:                           dest <- f(dest, src)
    mode = 1: [size: imm]               dest <- f(dest, imm)
    mode = 2: [address]                 dest <- f(dest, M[address])
    mode = 3: [address]                 M[address] <- f(M[address], src)
    mode = 4: [address]   [size: imm]   M[address] <- f(M[address], imm)
    else UND
    (dh and sh mark AH, BH, CH, or DH for dest or src)
    */
    fn read_binary_op(&mut self, get_a: bool, force_b_rm_sizecode: Option<u8>, force_b_imm_sizecode: Option<u8>) -> Result<(u8, u8, u64, u64, u64), ExecError> {
        let s1 = self.get_mem_adv_u8()?;
        let s2 = self.get_mem_adv_u8()?;
        let a_sizecode = (s1 >> 2) & 3;

        let (m, a, b) = match s2 >> 4 {
            0 => {
                let b_sizecode = force_b_rm_sizecode.unwrap_or(a_sizecode);
                let a = if !get_a { 0 } else if s1 & 2 != 0 { self.cpu.regs[s1 as usize >> 4].get_x8h() as u64 } else { self.cpu.regs[s1 as usize >> 4].raw_get(a_sizecode) };
                let b = if s1 & 1 != 0 { self.cpu.regs[s2 as usize & 15].get_x8h() as u64 } else { self.cpu.regs[s2 as usize & 15].raw_get(b_sizecode) };
                (0, a, b)
            }
            1 => {
                let b_sizecode = force_b_imm_sizecode.unwrap_or(a_sizecode);
                let a = if !get_a { 0 } else if s1 & 2 != 0 { self.cpu.regs[s1 as usize >> 4].get_x8h() as u64 } else { self.cpu.regs[s1 as usize >> 4].raw_get(a_sizecode) };
                let b = self.raw_get_mem_adv(b_sizecode)?;
                (0, a, b)
            }
            2 => {
                let b_sizecode = force_b_rm_sizecode.unwrap_or(a_sizecode);
                let a = if !get_a { 0 } else if s1 & 2 != 0 { self.cpu.regs[s1 as usize >> 4].get_x8h() as u64 } else { self.cpu.regs[s1 as usize >> 4].raw_get(a_sizecode) };
                let m = self.get_address_adv()?;
                let b = self.raw_get_mem(m, b_sizecode)?;
                (m, a, b)
            }
            3 => {
                let b_sizecode = force_b_rm_sizecode.unwrap_or(a_sizecode);
                let m = self.get_address_adv()?;
                let a = if !get_a { 0 } else { self.raw_get_mem(m, a_sizecode)? };
                let b = if s1 & 1 != 0 { self.cpu.regs[s2 as usize & 15].get_x8h() as u64 } else { self.cpu.regs[s2 as usize & 15].raw_get(b_sizecode) };
                (m, a, b)
            }
            4 => {
                let b_sizecode = force_b_imm_sizecode.unwrap_or(a_sizecode);
                let m = self.get_address_adv()?;
                let a = if !get_a { 0 } else { self.raw_get_mem(m, a_sizecode)? };
                let b = self.raw_get_mem_adv(b_sizecode)?;
                (m, a, b)
            }
            _ => return Err(ExecError::InvalidOpEncoding),
        };

        Ok((s1, s2, m, a, b))
    }
    fn store_binary_op_result(&mut self, s1: u8, s2: u8, m: u64, res: u64) -> Result<(), ExecError> {
        let sizecode = (s1 >> 2) & 3;
        if s2 <= 0x2f { // modes 0-2 -- this method avoids having to perform the shift
            if s1 & 2 != 0 { self.cpu.regs[s1 as usize >> 4].set_x8h(res as u8); } else { self.cpu.regs[s1 as usize >> 4].raw_set(sizecode, res); }
            Ok(())
        }
        else { self.raw_set_mem(m, sizecode, res) } // modes 3-4 -- the corresponding read already validated mode was in the proper range
    }

    /*
    [4: r1][2: size][1: r1h][1: mem]
    mem = 0: [1: r2h][3:][4: r2]   f(r1, r2)
    mem = 1: [address]             f(r1, M[address])
    (r1h and r2h mark AH, BH, CH, or DH for r1 or r2)
    */
    fn read_binary_lvalue_op(&mut self) -> Result<(u8, u64, u64, u64), ExecError> {
        let s = self.get_mem_adv_u8()?;
        let sizecode = (s >> 2) & 3;

        let a = if s & 2 != 0 { self.cpu.regs[s as usize >> 4].get_x8h() as u64 } else { self.cpu.regs[s as usize >> 4].raw_get(sizecode) };
        if s & 1 == 0 {
            let s2 = self.get_mem_adv_u8()?;
            let b = if s2 & 0x80 != 0 { self.cpu.regs[s2 as usize & 15].get_x8h() as u64 } else { self.cpu.regs[s2 as usize & 15].raw_get(sizecode) };
            Ok((s, s2 as u64, a, b))
        } else {
            let m = self.get_address_adv()?;
            let b = self.raw_get_mem(m, sizecode)?;
            Ok((s, m, a, b))
        }
    }
    fn store_binary_lvalue_result(&mut self, s: u8, sm2: u64, res1: u64, res2: u64) -> Result<(), ExecError> {
        let sizecode = (s >> 2) & 3;
        if s & 2 != 0 { self.cpu.regs[s as usize >> 4].set_x8h(res1 as u8); } else { self.cpu.regs[s as usize >> 4].raw_set(sizecode, res1); }
        if s & 1 == 0 {
            if sm2 & 0x80 != 0 { self.cpu.regs[sm2 as usize & 15].set_x8h(res2 as u8); } else { self.cpu.regs[sm2 as usize & 15].raw_set(sizecode, res2); }
            Ok(())
        } else {
            self.raw_set_mem(sm2, sizecode, res2)
        }
    }

    /*
    [4: dest][2: size][1: dh][1: mem]
    mem = 0:             dest <- f(dest)
    mem = 1: [address]   M[address] <- f(M[address])
    (dh marks AH, BH, CH, or DH for dest)
    */
    fn read_unary_op(&mut self, get: bool) -> Result<(u8, u64, u64), ExecError> {
        let s = self.get_mem_adv_u8()?;
        let sizecode = (s >> 2) & 3;

        let (m, v) = {
            if s & 1 == 0 {
                let v = if !get { 0 } else if s & 2 != 0 { self.cpu.regs[s as usize >> 4].get_x8h() as u64 } else { self.cpu.regs[s as usize >> 4].raw_get(sizecode) };
                (0, v)
            } else {
                let m = self.get_address_adv()?;
                let v = if !get { 0 } else { self.raw_get_mem(m, sizecode)? };
                (m, v)
            }
        };

        Ok((s, m, v))
    }
    fn store_unary_op_result(&mut self, s: u8, m: u64, res: u64) -> Result<(), ExecError> {
        let sizecode = (s >> 2) & 3;
        if s & 1 == 0 {
            if s & 2 != 0 { self.cpu.regs[s as usize >> 4].set_x8h(res as u8); } else { self.cpu.regs[s as usize >> 4].raw_set(sizecode, res); }
            Ok(())
        } else { self.raw_set_mem(m, sizecode, res) }
    }

    /*
    [4: reg][2: size][2: mode]
    mode = 0:               reg
    mode = 1:               h reg (AH, BH, CH, or DH)
    mode = 2: [size: imm]   imm
    mode = 3: [address]     M[address]
    */
    fn read_value_op(&mut self) -> Result<(u8, u64), ExecError> {
        let s = self.get_mem_adv_u8()?;
        let sizecode = (s >> 2) & 3;

        let v = match s & 3 {
            0 => self.cpu.regs[s as usize >> 4].raw_get(sizecode),
            1 => self.cpu.regs[s as usize >> 4].get_x8h() as u64,
            2 => self.raw_get_mem_adv(sizecode)?,
            3 => {
                let m = self.get_address_adv()?;
                self.raw_get_mem(m, sizecode)?
            }
            _ => unreachable!(),
        };

        Ok((s, v))
    }

    /*
    [cnd]
    cnd = 0: Z       cnd = 1: NZ
    cnd = 2: S       cnd = 3: NS
    cnd = 4: P       cnd = 5: NP
    cnd = 6: O       cnd = 7: NO
    cnd = 8: C       cnd = 9: NC
    cnd = 10: B      cnd = 11: BE
    cnd = 12: A      cnd = 13: AE
    cnd = 14: L      cnd = 15: LE
    cnd = 16: G      cnd = 17: GE
    cnd = 18: CXZ    cnd = 19: ECXZ
    cnd = 20: RCXZ
    else: UND
    */
    fn read_standard_condition(&mut self) -> Result<bool, ExecError> {
        Ok(match self.get_mem_adv_u8()? {
            0 => self.flags.get_zf(),
            1 => !self.flags.get_zf(),
            2 => self.flags.get_sf(),
            3 => !self.flags.get_sf(),
            4 => self.flags.get_pf(),
            5 => !self.flags.get_pf(),
            6 => self.flags.get_of(),
            7 => !self.flags.get_of(),
            8 => self.flags.get_cf(),
            9 => !self.flags.get_cf(),
            10 => self.flags.condition_b(),
            11 => self.flags.condition_be(),
            12 => self.flags.condition_a(),
            13 => self.flags.condition_ae(),
            14 => self.flags.condition_l(),
            15 => self.flags.condition_le(),
            16 => self.flags.condition_g(),
            17 => self.flags.condition_ge(),
            18 => self.cpu.get_cx() == 0,
            19 => self.cpu.get_ecx() == 0,
            20 => self.cpu.get_rcx() == 0,
            _ => return Err(ExecError::InvalidOpEncoding),
        })
    }

    // -------------------------------------------------------------------------------------

    /// Updates ZF SF PF to reflect the given value.
    /// Bits outside the range of the given size are ignored.
    fn update_flags_zsp(&mut self, value: u64, sizecode: u8) {
        self.flags.0 &= !mask!(Flags: MASK_ZF | MASK_SF | MASK_PF);
        if truncate(value, sizecode) == 0 { self.flags.set_zf(); }
        if sign_bit(value, sizecode) { self.flags.set_sf(); }
        if is_parity_even(value as u8) { self.flags.set_pf(); }
    }

    /// Randomizes the flags specified by the given mask.
    fn randomize_flags(&mut self, mask: u64) {
        self.flags.0 ^= self.rng.next_u64() & mask;
    }

    // -------------------------------------------------------------------------------------

    /*
    [4: dest][2: size][2:]   [address]
    dest <- address
    */
    fn exec_lea(&mut self) -> Result<(), ExecError> {
        let s = self.get_mem_adv_u8()?;
        let addr = self.get_address_adv()?;
        self.cpu.regs[s as usize >> 4].raw_set((s >> 2) & 3, addr);
        Ok(())
    }

    fn exec_mov(&mut self) -> Result<(), ExecError> {
        let (s1, s2, m, _, b) = self.read_binary_op(false, None, None)?;
        self.store_binary_op_result(s1, s2, m, b)
    }
    fn exec_movcc(&mut self) -> Result<(), ExecError> {
        let cnd = self.read_standard_condition()?;
        let (s1, s2, m, _, b) = self.read_binary_op(false, None, None)?;
        if cnd { self.store_binary_op_result(s1, s2, m, b) } else { Ok(()) }
    }
    fn exec_setcc(&mut self) -> Result<(), ExecError> {
        let cnd = self.read_standard_condition()?;
        let (s, m, _) = self.read_unary_op(false)?;
        self.store_unary_op_result(s, m, if cnd { 1 } else { 0 })
    }
    fn exec_xchg(&mut self) -> Result<(), ExecError> {
        let (s, sm2, a, b) = self.read_binary_lvalue_op()?;
        self.store_binary_lvalue_result(s, sm2, b, a)
    }

    /*
    [ext]
    ext =  0: stac
    ext =  1: clac
    ext =  2: cmac
    ext =  3: stc
    ext =  4: clc
    ext =  5: cmc
    ext =  6: std
    ext =  7: cld
    ext =  8: cmd
    ext =  9: sti
    ext = 10: cli
    ext = 11: cmi
    */
    fn exec_regop(&mut self) -> Result<(), ExecError> {
        match self.get_mem_adv_u8()? {
            0 => self.flags.set_ac(),
            1 => self.flags.clear_ac(),
            2 => self.flags.flip_ac(),
            3 => self.flags.set_cf(),
            4 => self.flags.clear_cf(),
            5 => self.flags.flip_cf(),
            6 => self.flags.set_df(),
            7 => self.flags.clear_df(),
            8 => self.flags.flip_df(),
            9 => self.flags.set_if(),
            10 => self.flags.clear_if(),
            11 => self.flags.flip_if(),
            _ => return Err(ExecError::InvalidOpEncoding),
        }
        Ok(())
    }

    fn exec_add(&mut self) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, None, None)?;
        let sizecode = (s1 >> 2) & 3;

        let res = truncate(a.wrapping_add(b), sizecode); // has to be truncated for CF logic

        self.update_flags_zsp(res, sizecode);
        self.flags.0 &= !mask!(Flags: MASK_CF | MASK_AF | MASK_OF);
        if res < a { self.flags.set_cf(); }
        if (res & 15) < (a & 15) { self.flags.set_af(); } // AF is just like CF but only the low 4-bits
        if sign_bit(!(a ^ b) & (a ^ res), sizecode) { self.flags.set_of(); } // overflow if sign(a)=sign(b) and sign(a)!=sign(res)
        
        self.store_binary_op_result(s1, s2, m, res)
    }
    fn exec_sub_helper(&mut self, should_store: bool) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, None, None)?;
        let sizecode = (s1 >> 2) & 3;

        let res = a.wrapping_sub(b);

        self.update_flags_zsp(res, sizecode);
        self.flags.0 &= !mask!(Flags: MASK_CF | MASK_AF | MASK_OF);
        if a < b { self.flags.set_cf(); } // if a < b then a borrow was taken from the highest bit
        if (a & 15) < (b & 15) { self.flags.set_af(); } // AF is just like CF but only the low 4-bits
        if sign_bit((a ^ b) & (a ^ res), sizecode) { self.flags.set_of(); } // overflow if sign(a)!=sign(b) and sign(a)!=sign(res)

        if should_store { self.store_binary_op_result(s1, s2, m, res) } else { Ok(()) }
    }
    fn exec_cmp0(&mut self) -> Result<(), ExecError> {
        let (s, _, v) = self.read_unary_op(true)?;
        let sizecode = (s >> 2) & 3;
        self.update_flags_zsp(v, sizecode);
        self.flags.0 &= !mask!(Flags: MASK_CF | MASK_OF | MASK_AF);
        Ok(())
    }

    /*
    [ext]
    ext = 0: mul 1
    ext = 1: mul 2
    ext = 2: mul 3
    ext = 3: mulx (3)
    ext = 4: imul 1
    ext = 5: imul 2
    ext = 6: imul 3
    ext = 7: imulx (3)
    ext = 8: div (1)
    ext = 9: idiv (1)
    else: UND
    */
    fn exec_muldiv_family(&mut self) -> Result<(), ExecError> {
        match self.get_mem_adv_u8()? {
            0 => self.exec_uimul_1(raw_mul),
            1 => self.exec_uimul_2(raw_mul),
            2 => self.exec_uimul_3(raw_mul),
            3 => self.exec_uimulx(raw_mul),
            4 => self.exec_uimul_1(raw_imul),
            5 => self.exec_uimul_2(raw_imul),
            6 => self.exec_uimul_3(raw_imul),
            7 => self.exec_uimulx(raw_imul),
            8 => self.exec_uidiv(raw_div),
            9 => self.exec_uidiv(raw_idiv),
            _ => Err(ExecError::InvalidOpEncoding),
        }
    }
    fn exec_uimul_1(&mut self, multiplier: fn(u8, u64, u64) -> (u64, u64, bool)) -> Result<(), ExecError> {
        let (s, v) = self.read_value_op()?;
        let sizecode = (s >> 2) & 3;
        let (high, low, overflow) = multiplier(sizecode, self.cpu.get_rax(), v);
        match sizecode {
            0 => { self.cpu.set_ax(low as u16); } // 16-bit result fits in 64-bit "low" half, so we can ignore high
            1 => { self.cpu.set_dx(high as u16); self.cpu.set_ax(low as u16); }
            2 => { self.cpu.set_edx(high as u32); self.cpu.set_eax(low as u32); }
            3 => { self.cpu.set_rdx(high); self.cpu.set_rax(low); }
            _ => unreachable!(),
        }
        let mask_co = mask!(Flags: MASK_CF | MASK_OF);
        if overflow { self.flags.0 |= mask_co } else { self.flags.0 &= !mask_co }
        self.randomize_flags(mask!(Flags: MASK_SF | MASK_ZF | MASK_AF | MASK_PF));
        Ok(())
    }
    fn exec_uimul_2(&mut self, multiplier: fn(u8, u64, u64) -> (u64, u64, bool)) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, None, None)?;
        let (_, res, overflow) = multiplier((s1 >> 2) & 3, a, b);
        let mask_co = mask!(Flags: MASK_CF | MASK_OF);
        if overflow { self.flags.0 |= mask_co } else { self.flags.0 &= !mask_co }
        self.randomize_flags(mask!(Flags: MASK_SF | MASK_ZF | MASK_AF | MASK_PF));
        self.store_binary_op_result(s1, s2, m, res)
    }
    fn exec_uimul_3(&mut self, multiplier: fn(u8, u64, u64) -> (u64, u64, bool)) -> Result<(), ExecError> {
        let (s1, s2, s3, m, a, b) = self.read_ternary_op(true, None, None)?;
        let (_, res, overflow) = multiplier((s2 >> 2) & 3, a, b);
        let mask_co = mask!(Flags: MASK_CF | MASK_OF);
        if overflow { self.flags.0 |= mask_co } else { self.flags.0 &= !mask_co }
        self.randomize_flags(mask!(Flags: MASK_SF | MASK_ZF | MASK_AF | MASK_PF));
        self.store_ternary_op_result(s1, s2, s3, m, res, None)
    }
    fn exec_uimulx(&mut self, multiplier: fn(u8, u64, u64) -> (u64, u64, bool)) -> Result<(), ExecError> {
        let (s1, s2, s3, m, _, v) = self.read_ternary_op(false, None, None)?;
        let sizecode = (s2 >> 2) & 3;
        let (high, low, _) = multiplier(sizecode, self.cpu.get_rdx(), v);
        self.store_ternary_op_result(s1, s2, s3, m, high, Some(low))
    }
    fn exec_uidiv(&mut self, divider: fn(u8, u128, u64) -> (u64, u64, bool)) -> Result<(), ExecError> {
        let (s, v) = self.read_value_op()?;
        let sizecode = (s >> 2) & 3;
        debug_assert!(truncate(v, sizecode) == v);
        if v == 0 { return Err(ExecError::DivideByZero); }
        let num = match sizecode {
            0 => self.cpu.get_ax() as u128,
            1 => ((self.cpu.get_dx() as u128) << 16) | self.cpu.get_ax() as u128,
            2 => ((self.cpu.get_edx() as u128) << 32) | self.cpu.get_eax() as u128,
            3 => ((self.cpu.get_rdx() as u128) << 64) | self.cpu.get_rax() as u128,
            _ => unreachable!(),
        };
        let (quo, rem, overflow) = divider(sizecode, num, v);
        if overflow { return Err(ExecError::DivisionOverflow); }
        match sizecode {
            0 => self.cpu.set_ax(((rem << 8) | quo) as u16),
            1 => { self.cpu.set_dx(rem as u16); self.cpu.set_ax(quo as u16); }
            2 => { self.cpu.set_edx(rem as u32); self.cpu.set_eax(quo as u32); }
            3 => { self.cpu.set_rdx(rem as u64); self.cpu.set_rax(quo as u64); }
            _ => unreachable!(),
        }
        self.randomize_flags(mask!(Flags: MASK_CF | MASK_OF | MASK_SF | MASK_ZF | MASK_AF | MASK_PF));
        Ok(())
    }

    fn exec_and_helper(&mut self, should_store: bool) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, None, None)?;
        let sizecode = (s1 >> 2) & 3;

        let res = a & b;

        self.flags.0 &= !mask!(Flags: MASK_OF | MASK_CF);
        self.update_flags_zsp(res, sizecode);
        self.randomize_flags(mask!(Flags: MASK_AF));
        
        if should_store { self.store_binary_op_result(s1, s2, m, res) } else { Ok(()) }
    }
    fn exec_or(&mut self) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, None, None)?;
        let sizecode = (s1 >> 2) & 3;

        let res = a | b;

        self.flags.0 &= !mask!(Flags: MASK_OF | MASK_CF);
        self.update_flags_zsp(res, sizecode);
        self.randomize_flags(mask!(Flags: MASK_AF));
        
        self.store_binary_op_result(s1, s2, m, res)
    }
    fn exec_xor(&mut self) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, None, None)?;
        let sizecode = (s1 >> 2) & 3;

        let res = a ^ b;

        self.flags.0 &= !mask!(Flags: MASK_OF | MASK_CF);
        self.update_flags_zsp(res, sizecode);
        self.randomize_flags(mask!(Flags: MASK_AF));
        
        self.store_binary_op_result(s1, s2, m, res)
    }

    /*
    [ext]
    ext = 0: shl
    ext = 1: shr
    ext = 2: sar
    ext = 3: rol
    ext = 4: ror
    ext = 5: rcl
    ext = 6: rcr
    ext = 7: shlx
    ext = 8: shrx
    ext = 9: sarx
    ext = 10: bt
    ext = 11: btc
    ext = 12: btr
    ext = 13: bts
    */
    fn exec_bitwise(&mut self) -> Result<(), ExecError> {
        match self.get_mem_adv_u8()? {
            0 => self.exec_shift(|_, m| m, |sizecode, val, masked, _| {
                debug_assert!(masked < 64 && masked > 0);
                let bits = 8u32 << sizecode;
                let res = val << masked;
                let carry = val.wrapping_shr(bits.wrapping_sub(masked)) & 1 != 0;
                debug_assert!(masked <= bits || !carry); // masked > bits -> !carry
                let overflow = sign_bit(res, sizecode) ^ carry;
                (res, carry, overflow)
            }),
            1 => self.exec_shift(|_, m| m, |sizecode, val, masked, _| {
                debug_assert!(masked < 64 && masked > 0);
                let res = val >> masked;
                let carry = (val >> (masked - 1)) & 1 != 0;
                let overflow = sign_bit(val, sizecode);
                (res, carry, overflow)
            }),
            2 => self.exec_shift(|_, m| m, |sizecode, val, masked, _| {
                debug_assert!(masked < 64 && masked > 0);
                let extended = sign_extend(val, sizecode) as i64;
                let res = (extended >> masked) as u64;
                let carry = (extended >> (masked - 1)) & 1 != 0;
                (res, carry, false)
            }),
            3 => self.exec_shift(|sizecode, masked| masked & ((8 << sizecode) - 1), |sizecode, val, masked, _| {
                debug_assert!(masked < 64 && masked > 0);
                let res = match sizecode {
                    0 => (val as u8).rotate_left(masked) as u64,
                    1 => (val as u16).rotate_left(masked) as u64,
                    2 => (val as u32).rotate_left(masked) as u64,
                    3 => (val as u64).rotate_left(masked) as u64,
                    _ => unreachable!(),
                };
                let carry = res & 1 != 0;
                let overflow = sign_bit(res, sizecode) ^ carry;
                (res, carry, overflow)
            }),
            4 => self.exec_shift(|sizecode, masked| masked & ((8 << sizecode) - 1), |sizecode, val, masked, _| {
                debug_assert!(masked < 64 && masked > 0);
                let res = match sizecode {
                    0 => (val as u8).rotate_right(masked) as u64,
                    1 => (val as u16).rotate_right(masked) as u64,
                    2 => (val as u32).rotate_right(masked) as u64,
                    3 => (val as u64).rotate_right(masked) as u64,
                    _ => unreachable!(),
                };
                let carry = (val >> (masked - 1)) & 1 != 0;
                let overflow = sign_bit(res ^ (res << 1), sizecode);
                (res, carry, overflow)
            }),
            5 => self.exec_shift(|sizecode, masked| masked % ((8 << sizecode) + 1), |sizecode, val, masked, cf| {
                let bits = (8 << sizecode) + 1;
                debug_assert!(masked < bits && masked < 64 && masked > 0); // should be guaranteed by maskmod
                let lower = if masked > 1 { val >> (bits - masked) } else { 0 };
                let upper = ((val << 1) | (if cf { 1 } else { 0 })) << (masked - 1);
                let res = upper | lower;
                let carry = (val >> (bits - masked - 1)) & 1 != 0;
                let overflow = sign_bit(res, sizecode) ^ carry;
                (res, carry, overflow)
            }),
            6 => self.exec_shift(|sizecode, masked| masked % ((8 << sizecode) + 1), |sizecode, val, masked, cf| {
                let bits = (8 << sizecode) + 1;
                debug_assert!(masked < bits && masked < 64 && masked > 0); // should be guaranteed by maskmod
                let lower = ((val >> 1) | (if cf { 1 << (bits - 2) } else { 0 })) >> (masked - 1);
                let upper = if masked > 1 { val << (bits - masked) } else { 0 };
                let res = upper | lower;
                let carry = (val >> (masked - 1)) & 1 != 0;
                let overflow = sign_bit(res ^ (res << 1), sizecode);
                (res, carry, overflow)
            }),
            7 => self.exec_shiftx(|_, val, masked| val << masked),
            8 => self.exec_shiftx(|_, val, masked| val >> masked),
            9 => self.exec_shiftx(|sizecode, val, masked| ((sign_extend(val, sizecode) as i64) >> masked) as u64),
            10 => self.exec_bit_test(None),
            11 => self.exec_bit_test(Some(|v, m| v ^ m)),
            12 => self.exec_bit_test(Some(|v, m| v & !m)),
            13 => self.exec_bit_test(Some(|v, m| v | m)),
            _ => Err(ExecError::InvalidOpEncoding),
        }
    }
    fn exec_bit_test(&mut self, mutator: Option<fn(u64, u64) -> u64>) -> Result<(), ExecError> {
        let (s1, s2, mut m, mut a, b) = self.read_binary_op(true, None, Some(0))?;
        let sizecode = (s1 >> 2) & 3;
        let bits = 1 << (3 + sizecode);
        debug_assert!(s2 >> 4 <= 4); // future proof for any new binary op modes

        // if it's a memory operation on a non-local block
        if s2 >> 4 >= 3 && b >= bits {
            m = m.wrapping_add((b >> (3 + sizecode)) << sizecode); // (b / bits) * bytes
            a = self.raw_get_mem(m, sizecode)?;
        }

        let mask = 1 << (b & (bits - 1));
        self.flags.assign_cf(a & mask != 0);
        self.randomize_flags(mask!(Flags: MASK_OF | MASK_SF | MASK_AF | MASK_PF));
        match mutator {
            Some(f) => self.store_binary_op_result(s1, s2, m, f(a, mask)),
            None => Ok(())
        }
    }
    fn exec_shift(&mut self, maskmod: fn(u8, u32) -> u32, shifter: fn(u8, u64, u32, bool) -> (u64, bool, bool)) -> Result<(), ExecError> {
        let (s1, s2, m, a, b) = self.read_binary_op(true, Some(0), Some(0))?;
        let sizecode = (s1 >> 2) & 3;
        let masked = maskmod(sizecode, b as u32 & (if sizecode >= 3 { 0x3f } else { 0x1f }));
        if masked == 0 { return Ok(()) }
        debug_assert_eq!(a, truncate(a, sizecode)); // shifters assume this

        let (res, carry, overflow) = shifter(sizecode, a, masked, self.flags.get_cf());
        let mut randomize_mask = mask!(Flags: MASK_AF);
        self.flags.assign_cf(carry); // technically if masked >= bits, CF is UND for SHL and SHR, but not for SAR - we arbitrarily let them all be well-defined
        if masked == 1 { self.flags.assign_of(overflow); } else { randomize_mask |= mask!(Flags: MASK_OF); }
        self.update_flags_zsp(res, sizecode);
        self.randomize_flags(randomize_mask);

        self.store_binary_op_result(s1, s2, m, res)
    }
    fn exec_shiftx(&mut self, shifter: fn(u8, u64, u32) -> u64) -> Result<(), ExecError> {
        let (s1, s2, s3, m, a, b) = self.read_ternary_op(true, None, Some(0))?;
        let sizecode = (s2 >> 2) & 3;
        let masked = b as u32 & (if sizecode >= 3 { 0x3f } else { 0x1f });
        let res = shifter(sizecode, a, masked);
        self.store_ternary_op_result(s1, s2, s3, m, res, None)
    }

    fn exec_jmp(&mut self) -> Result<(), ExecError> {
        let (_, v) = self.read_value_op()?;
        self.jump_to(v)
    }
    fn exec_jcc(&mut self) -> Result<(), ExecError> {
        let cnd = self.read_standard_condition()?;
        let (_, v) = self.read_value_op()?;
        if cnd { self.jump_to(v) } else { Ok(()) }
    }
    fn exec_loopcc(&mut self) -> Result<(), ExecError> {
        let cnd = match self.get_mem_adv_u8()? {
            0 => true,
            1 => self.flags.get_zf(),
            2 => !self.flags.get_zf(),
            _ => return Err(ExecError::InvalidOpEncoding),
        };
        let (_, v) = self.read_value_op()?;
        let new_rcx = self.cpu.get_rcx().wrapping_sub(1);
        self.cpu.set_rcx(new_rcx);
        if new_rcx != 0 && cnd { self.jump_to(v) } else { Ok(()) }
    }
    fn exec_call(&mut self) -> Result<(), ExecError> {
        let (_, v) = self.read_value_op()?;
        let aft = self.instruction_pointer;
        self.jump_to(v)?;
        self.push_mem_u64(aft as u64)
    }
    fn exec_ret(&mut self) -> Result<(), ExecError> {
        let v = self.pop_mem_u64()?;
        self.jump_to(v)
    }

    fn exec_push(&mut self) -> Result<(), ExecError> {
        let (s, v) = self.read_value_op()?;
        let sizecode = (s >> 2) & 3;
        self.raw_push_mem(sizecode, v)
    }
    fn exec_pop(&mut self) -> Result<(), ExecError> {
        let (s, m, _) = self.read_unary_op(false)?;
        let sizecode = (s >> 2) & 3;
        let res = self.raw_pop_mem(sizecode)?;
        self.store_unary_op_result(s, m, res)
    }

    fn exec_inc(&mut self) -> Result<(), ExecError> {
        let (s, m, v) = self.read_unary_op(true)?;
        let sizecode = (s >> 2) & 3;

        let res = truncate(v.wrapping_add(1), sizecode); // truncated for carry flag check below

        self.flags.0 &= !mask!(Flags: MASK_AF | MASK_OF);
        self.update_flags_zsp(res, sizecode);
        if res & 0x0f == 0 { self.flags.set_af(); } // low nibble of 0 was a nibble overflow (TM)
        if sign_bit(!v & res, sizecode) { self.flags.set_of(); }

        self.store_unary_op_result(s, m, res)
    }
    fn exec_dec(&mut self) -> Result<(), ExecError> {
        let (s, m, v) = self.read_unary_op(true)?;
        let sizecode = (s >> 2) & 3;

        let res = truncate(v.wrapping_sub(1), sizecode); // truncated for carry flag check below

        self.flags.0 &= !mask!(Flags: MASK_AF | MASK_OF);
        self.update_flags_zsp(res, sizecode);
        if v & 0x0f == 0 { self.flags.set_af(); } // low nibble of 0 was a nibble underflow (TM)
        if sign_bit(v & !res, sizecode) { self.flags.set_of(); }

        self.store_unary_op_result(s, m, res)
    }
    fn exec_neg(&mut self) -> Result<(), ExecError> {
        let (s, m, v) = self.read_unary_op(true)?;
        let sizecode = (s >> 2) & 3;

        let res = truncate(v.wrapping_neg(), sizecode); // truncated for flag check below

        self.flags.0 &= !mask!(Flags: MASK_CF | MASK_AF | MASK_OF);
        self.update_flags_zsp(res, sizecode);
        if v != 0 { self.flags.set_cf(); } // this is 0 < v (see exec_sub() logic for 0 - v)
        if v & 0x0f != 0 { self.flags.set_af(); }               // same reasoning as above, but only low nibble
        if sign_bit(v & res, sizecode) { self.flags.set_of(); } // same reasoning as above

        self.store_unary_op_result(s, m, res)
    }
    fn exec_not(&mut self) -> Result<(), ExecError> {
        let (s, m, v) = self.read_unary_op(true)?;
        self.store_unary_op_result(s, m, !v)
    }

    fn exec_string_rep(&mut self, sizecode: u8, func: fn(&mut Self, u8) -> Result<(), ExecError>) -> Result<(), ExecError> { impl_string_repeat!(self, sizecode, func, true) }
    fn exec_string_repe(&mut self, sizecode: u8, func: fn(&mut Self, u8) -> Result<(), ExecError>) -> Result<(), ExecError> { impl_string_repeat!(self, sizecode, func, self.flags.get_zf()) }
    fn exec_string_repne(&mut self, sizecode: u8, func: fn(&mut Self, u8) -> Result<(), ExecError>) -> Result<(), ExecError> { impl_string_repeat!(self, sizecode, func, !self.flags.get_zf()) }

    /*
    [6: mode][2: size]
        mode = 0:        MOVS
        mode = 1:  REP   MOVS
        mode = 2:        CMPS
        mode = 3:  REPE  CMPS
        mode = 4:  REPNE CMPS
        mode = 5:        LODS
        mode = 6:  REP   LODS
        mode = 7:        STOS
        mode = 8:  REP   STOS
        mode = 9:        SCAS
        mode = 10: REPE  SCAS
        mode = 11: REPNE SCAS
        else UND
    */
    fn exec_string(&mut self) -> Result<(), ExecError> {
        let s = self.get_mem_adv_u8()?;
        let sizecode = s & 3;
        match s >> 2 {
            0 => self.exec_string_movs(sizecode),
            1 => self.exec_string_rep(sizecode, Self::exec_string_movs),
            _ => Err(ExecError::InvalidOpEncoding),
        }
    }
    fn exec_string_movs(&mut self, sizecode: u8) -> Result<(), ExecError> {
        let rdi = self.cpu.get_rdi();
        let rsi = self.cpu.get_rsi();

        let temp = self.raw_get_mem(rsi, sizecode)?;
        self.raw_set_mem(rdi, sizecode, temp)?;

        if self.flags.get_df() {
            self.cpu.set_rdi(rdi.wrapping_sub(1 << sizecode));
            self.cpu.set_rsi(rsi.wrapping_sub(1 << sizecode));
        } else {
            self.cpu.set_rdi(rdi.wrapping_add(1 << sizecode));
            self.cpu.set_rsi(rsi.wrapping_add(1 << sizecode));
        }

        Ok(())
    }

    fn get_cpu_debug_string(&self) -> String {
        format!(
r"rax: {:016x}  r8: {:016x}
rbx: {:016x}  r9: {:016x}
rcx: {:016x} r10: {:016x}
rdx: {:016x} r11: {:016x}
rsi: {:016x} r12: {:016x}
rdi: {:016x} r13: {:016x}
rbp: {:016x} r14: {:016x}
rsp: {:016x} r15: {:016x}",
            self.cpu.get_rax(), self.cpu.get_r8(),
            self.cpu.get_rbx(), self.cpu.get_r9(),
            self.cpu.get_rcx(), self.cpu.get_r10(),
            self.cpu.get_rdx(), self.cpu.get_r11(),
            self.cpu.get_rsi(), self.cpu.get_r12(),
            self.cpu.get_rdi(), self.cpu.get_r13(),
            self.cpu.get_rbp(), self.cpu.get_r14(),
            self.cpu.get_rsp(), self.cpu.get_r15(),
        )
    }
    fn exec_debug(&mut self) -> Result<(), ExecError> {
        match self.get_mem_adv_u8()? {
            0 => eprintln!("\n{}", self.get_cpu_debug_string()),
            _ => return Err(ExecError::InvalidOpEncoding),
        }
        Ok(())
    }
}
impl Default for Emulator {
    fn default() -> Self {
        Emulator::new()
    }
}