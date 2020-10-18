//! Everything pertaining to executing CSX64 executables.

use rand_xorshift::XorShiftRng;
use rand_core::SeedableRng;
use getrandom::getrandom;
use memchr::memchr;

use std::mem;
use std::convert::TryInto;

use crate::common::f80::*;

pub mod registers;
pub mod fpu;
pub mod fd;

use registers::*;
use fpu::*;
use fd::*;

/// Bitmask denoting RFLAGS that users can modify with instructions like POPF.
pub const MODIFIABLE_FLAGS: u64 = 0x003f0fd5;

/// Default number of file descriptors.
const DEFAULT_MAX_FD: usize = 16;
/// Default max on emulator main memory footprint.
const DEFAULT_MAX_MEM: usize = 2 * 1024 * 1024 * 1024;

/// Current state of an emulator.
pub enum State {
    /// The emulator has not been initialized with a program to run.
    Uninitialized,
    /// The emulator is still running.
    Running,
    /// The emulator terminated successfully with the given program return code.
    Terminated(i32),
    /// The emulator terminated due to an error.
    Error(ExecError),
}

#[derive(Clone, Copy, Debug)]
pub enum ExecError {
    MemOutOfBounds,
    StackOverflow, StackUnderflow,
    WriteInReadonlyMemory,
}

macro_rules! register_aliases {
    ($src:ident => $([ $idx:literal : $t:ty => $get:ident : $getf:ident , $set:ident : $setf:ident ]),*$(,)?) => {$(
        pub fn $get(&self) -> $t {
            self.$src[$idx].$getf()
        }
        pub fn $set(&mut self, val: $t) {
            self.$src[$idx].$setf(val)
        }
    )*}
}

macro_rules! impl_mem_primitive {
    ($([ $get:ident : $set:ident : $push:ident : $pop:ident => $t:ty ]),*$(,)?) => {$(
        pub fn $get(&self, pos: u64) -> Result<$t, ExecError> {
            if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
            let pos = pos as usize;

            match self.memory.get(pos..pos.wrapping_add(mem::size_of::<$t>())) {
                None => Err(ExecError::MemOutOfBounds), // this also handles overflow of sum
                Some(bin) => Ok(<$t>::from_le_bytes(bin.try_into().unwrap())),
            }
        }
        pub fn $set(&mut self, pos: u64, val: $t) -> Result<(), ExecError> {
            if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
            let pos = pos as usize;

            if pos < self.readonly_barrier { return Err(ExecError::WriteInReadonlyMemory); }
            match self.memory.get_mut(pos..pos.wrapping_add(mem::size_of::<$t>())) {
                None => Err(ExecError::MemOutOfBounds), // this also handles overflow of sum
                Some(bin) => Ok(bin.copy_from_slice(&val.to_le_bytes())),
            }
        }
        pub fn $push(&mut self, val: $t) -> Result<(), ExecError> {
            let pos = self.get_rsp().wrapping_sub(mem::size_of::<$t>() as u64);
            if pos < self.stack_barrier as u64 { return Err(ExecError::StackOverflow); }
            self.$set(pos, val)?;
            self.set_rsp(pos);
            Ok(())
        }
        pub fn $pop(&mut self) -> Result<$t, ExecError> {
            let pos = self.get_rsp();
            let next_pos = pos.wrapping_add(mem::size_of::<$t>() as u64);
            if next_pos > self.heap_barrier as u64 { return Err(ExecError::StackUnderflow); }
            let res = self.$get(pos)?;
            self.set_rsp(next_pos);
            Ok(res)
        }
    )*}
}

macro_rules! impl_mem_adv_primitive {
    ($([ $get_adv:ident : $t:ty => $f:ident  ]),*$(,)?) => {$(
        fn $get_adv(&mut self) -> Result<$t, ExecError> {
            let res = self.$f(self.instruction_pointer as u64)?;
            self.instruction_pointer += mem::size_of::<$t>(); // success of read implies this won't overflow
            Ok(res)
        }
    )*}
}

pub struct Emulator {
    state: State,
    instruction_pointer: usize,

    cpu_regs: [CPURegister; 16],
    vpu_regs: [ZMMRegister; 32],
    fpu: FPU,

    flags: RFLAGS,
    mxcsr: MXCSR,

    memory: Vec<u8>,
    min_memory: usize, // so users can't accidentally truncate the executable itself
    max_memory: usize,

    exe_barrier: usize,      // barrier before which memory is executable
    readonly_barrier: usize, // barrier before which memory is read-only (>= exe_barrier)
    stack_barrier: usize,    // barrier between program and stack (stack crossing is stack overflow)
    heap_barrier: usize,     // barrier between stack and heap (stack crossing is stack underflow)

    file_descriptors: Vec<Box<dyn FileDescriptor>>,

    rng: XorShiftRng,
}
impl Emulator {
    /// Creates a new emulator in the uninitialized state.
    pub fn new() -> Emulator {
        Emulator {
            state: State::Uninitialized,
            instruction_pointer: 0,

            cpu_regs: Default::default(),
            vpu_regs: Default::default(),
            fpu: Default::default(),

            flags: RFLAGS(0),
            mxcsr: MXCSR(0),

            memory: vec![],
            min_memory: 0,
            max_memory: 0,

            exe_barrier: 0,
            readonly_barrier: 0,
            stack_barrier: 0,
            heap_barrier: 0,

            file_descriptors: vec![],

            rng: XorShiftRng::from_seed({ let mut s = <<XorShiftRng as SeedableRng>::Seed>::default(); getrandom(s.as_mut()).unwrap(); s }),
        }
    }

    // -------------------------------------------------------------------------------------

    /// Checks the "below" condition from flags.
    pub fn condition_b(&self) -> bool { self.flags.get_cf() }
    /// Checks the "below or equal" condition from flags.
    pub fn condition_be(&self) -> bool { self.flags.get_cf() || self.flags.get_zf() }
    /// Checks the "above" condition from flags.
    pub fn condition_a(&self) -> bool { !self.condition_be() }
    /// Checks the "above or equal" condition from flags.
    pub fn condition_ae(&self) -> bool { !self.condition_b() }

    // -------------------------------------------------------------------------------------

    /// Checks the "less than" condition from flags.
    pub fn condition_l(&self) -> bool { self.flags.get_sf() != self.flags.get_of() }
    /// Checks the "less or equal" condition from flags.
    pub fn condition_le(&self) -> bool { self.flags.get_zf() || (self.flags.get_sf() != self.flags.get_of()) }
    /// Checks the "greater than" condition from flags.
    pub fn condition_g(&self) -> bool { !self.condition_le() }
    /// Checks the "greater or equal" condition from flags.
    pub fn condition_ge(&self) -> bool { !self.condition_l() }

    // -------------------------------------------------------------------------------------

    register_aliases! { cpu_regs => 
        [  0:u64 => get_rax:get_x64, set_rax:set_x64 ],
        [  1:u64 => get_rbx:get_x64, set_rbx:set_x64 ],
        [  2:u64 => get_rcx:get_x64, set_rcx:set_x64 ],
        [  3:u64 => get_rdx:get_x64, set_rdx:set_x64 ],
        [  4:u64 => get_rsi:get_x64, set_rsi:set_x64 ],
        [  5:u64 => get_rdi:get_x64, set_rdi:set_x64 ],
        [  6:u64 => get_rbp:get_x64, set_rbp:set_x64 ],
        [  7:u64 => get_rsp:get_x64, set_rsp:set_x64 ],
        [  8:u64 => get_r8:get_x64,  set_r8:set_x64 ],
        [  9:u64 => get_r9:get_x64,  set_r9:set_x64 ],
        [ 10:u64 => get_r10:get_x64, set_r10:set_x64 ],
        [ 11:u64 => get_r11:get_x64, set_r11:set_x64 ],
        [ 12:u64 => get_r12:get_x64, set_r12:set_x64 ],
        [ 13:u64 => get_r13:get_x64, set_r13:set_x64 ],
        [ 14:u64 => get_r14:get_x64, set_r14:set_x64 ],
        [ 15:u64 => get_r15:get_x64, set_r15:set_x64 ],

        [  0:u32 => get_eax:get_x32,  set_eax:set_x32 ],
        [  1:u32 => get_ebx:get_x32,  set_ebx:set_x32 ],
        [  2:u32 => get_ecx:get_x32,  set_ecx:set_x32 ],
        [  3:u32 => get_edx:get_x32,  set_edx:set_x32 ],
        [  4:u32 => get_esi:get_x32,  set_esi:set_x32 ],
        [  5:u32 => get_edi:get_x32,  set_edi:set_x32 ],
        [  6:u32 => get_ebp:get_x32,  set_ebp:set_x32 ],
        [  7:u32 => get_esp:get_x32,  set_esp:set_x32 ],
        [  8:u32 => get_r8d:get_x32,  set_r8d:set_x32 ],
        [  9:u32 => get_r9d:get_x32,  set_r9d:set_x32 ],
        [ 10:u32 => get_r10d:get_x32, set_r10d:set_x32 ],
        [ 11:u32 => get_r11d:get_x32, set_r11d:set_x32 ],
        [ 12:u32 => get_r12d:get_x32, set_r12d:set_x32 ],
        [ 13:u32 => get_r13d:get_x32, set_r13d:set_x32 ],
        [ 14:u32 => get_r14d:get_x32, set_r14d:set_x32 ],
        [ 15:u32 => get_r15d:get_x32, set_r15d:set_x32 ],

        [  0:u16 => get_ax:get_x16,   set_ax:set_x16 ],
        [  1:u16 => get_bx:get_x16,   set_bx:set_x16 ],
        [  2:u16 => get_cx:get_x16,   set_cx:set_x16 ],
        [  3:u16 => get_dx:get_x16,   set_dx:set_x16 ],
        [  4:u16 => get_si:get_x16,   set_si:set_x16 ],
        [  5:u16 => get_di:get_x16,   set_di:set_x16 ],
        [  6:u16 => get_bp:get_x16,   set_bp:set_x16 ],
        [  7:u16 => get_sp:get_x16,   set_sp:set_x16 ],
        [  8:u16 => get_r8w:get_x16,  set_r8w:set_x16 ],
        [  9:u16 => get_r9w:get_x16,  set_r9w:set_x16 ],
        [ 10:u16 => get_r10w:get_x16, set_r10w:set_x16 ],
        [ 11:u16 => get_r11w:get_x16, set_r11w:set_x16 ],
        [ 12:u16 => get_r12w:get_x16, set_r12w:set_x16 ],
        [ 13:u16 => get_r13w:get_x16, set_r13w:set_x16 ],
        [ 14:u16 => get_r14w:get_x16, set_r14w:set_x16 ],
        [ 15:u16 => get_r15w:get_x16, set_r15w:set_x16 ],

        [  0:u8 => get_al:get_x8,   set_al:set_x8 ],
        [  1:u8 => get_bl:get_x8,   set_bl:set_x8 ],
        [  2:u8 => get_cl:get_x8,   set_cl:set_x8 ],
        [  3:u8 => get_dl:get_x8,   set_dl:set_x8 ],
        [  4:u8 => get_sil:get_x8,  set_sil:set_x8 ],
        [  5:u8 => get_dil:get_x8,  set_dil:set_x8 ],
        [  6:u8 => get_bpl:get_x8,  set_bpl:set_x8 ],
        [  7:u8 => get_spl:get_x8,  set_spl:set_x8 ],
        [  8:u8 => get_r8b:get_x8,  set_r8b:set_x8 ],
        [  9:u8 => get_r9b:get_x8,  set_r9b:set_x8 ],
        [ 10:u8 => get_r10b:get_x8, set_r10b:set_x8 ],
        [ 11:u8 => get_r11b:get_x8, set_r11b:set_x8 ],
        [ 12:u8 => get_r12b:get_x8, set_r12b:set_x8 ],
        [ 13:u8 => get_r13b:get_x8, set_r13b:set_x8 ],
        [ 14:u8 => get_r14b:get_x8, set_r14b:set_x8 ],
        [ 15:u8 => get_r15b:get_x8, set_r15b:set_x8 ],

        [ 0:u8 => get_ah:get_x8h, set_ah:set_x8h ],
        [ 1:u8 => get_bh:get_x8h, set_bh:set_x8h ],
        [ 2:u8 => get_ch:get_x8h, set_ch:set_x8h ],
        [ 3:u8 => get_dh:get_x8h, set_dh:set_x8h ],
    }

    // -------------------------------------------------------------------------------------

    impl_mem_primitive! {
        [ get_mem_u8   : set_mem_u8   : push_mem_u8   : pop_mem_u8   => u8 ],
        [ get_mem_u16  : set_mem_u16  : push_mem_u16  : pop_mem_u16  => u16 ],
        [ get_mem_u32  : set_mem_u32  : push_mem_u32  : pop_mem_u32  => u32 ],
        [ get_mem_u64  : set_mem_u64  : push_mem_u64  : pop_mem_u64  => u64 ],

        [ get_mem_i8   : set_mem_i8   : push_mem_i8   : pop_mem_i8   => i8 ],
        [ get_mem_i16  : set_mem_i16  : push_mem_i16  : pop_mem_i16  => i16 ],
        [ get_mem_i32  : set_mem_i32  : push_mem_i32  : pop_mem_i32  => i32 ],
        [ get_mem_i64  : set_mem_i64  : push_mem_i64  : pop_mem_i64  => i64 ],

        [ get_mem_f32 : set_mem_f32 : push_mem_f32 : pop_mem_f32 => f32 ],
        [ get_mem_f64 : set_mem_f64 : push_mem_f64 : pop_mem_f64 => f64 ],
    }

    pub fn get_mem_f80(&self, pos: u64) -> Result<F80, ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let pos = pos as usize;

        match self.memory.get(pos..pos.wrapping_add(10)) {
            None => Err(ExecError::MemOutOfBounds), // this also handles overflow of sum
            Some(bin) => Ok(F80(bin.try_into().unwrap())),
        }
    }
    pub fn set_mem_f80(&mut self, pos: u64, val: F80) -> Result<(), ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let pos = pos as usize;

        if pos < self.readonly_barrier { return Err(ExecError::WriteInReadonlyMemory); }
        match self.memory.get_mut(pos..pos.wrapping_add(10)) {
            None => return Err(ExecError::MemOutOfBounds), // this also handles overflow of sum
            Some(bin) => Ok(bin.copy_from_slice(&val.0)),
        }
    }

    /// Reads a null-terminated binary string starting at the given position.
    /// The null terminator is not included in the result.
    /// If pos itself is a null terminator, returns an empty slice.
    /// Fails if no null terminator is found or the range goes out of bounds.
    pub fn get_null_term_bin(&self, pos: u64) -> Result<&[u8], ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let pos = pos as usize;

        if pos >= self.memory.len() { return Err(ExecError::MemOutOfBounds); }
        match memchr(0, &self.memory[pos..]) {
            None => Err(ExecError::MemOutOfBounds),
            Some(stop) => Ok(&self.memory[pos..stop]),
        }
    }
    /// Writes a null-terminated binary string to the given position.
    /// Note that the value need not be null terminated: we simply append a terminator in the internal representation.
    /// Indeed, zeros in the value are included verbatim, though they will not be present with the matching read function.
    /// Fails if the result goes out of bounds or intersects readonly memory.
    pub fn set_null_term_bin(&mut self, pos: u64, value: &[u8]) -> Result<(), ExecError> {
        if pos > usize::MAX as u64 { return Err(ExecError::MemOutOfBounds); }
        let pos = pos as usize;

        if pos < self.readonly_barrier { return Err(ExecError::WriteInReadonlyMemory); }
        let stop = pos.wrapping_add(value.len());
        if stop >= self.memory.len() { return Err(ExecError::MemOutOfBounds); } // make sure we can boop a terminator on the end
        match self.memory.get_mut(pos..stop) {
            None => return Err(ExecError::MemOutOfBounds), // this also handles overflow of stop sum
            Some(dest) => {
                dest.copy_from_slice(value);
                self.memory[stop] = 0;
                Ok(())
            }
        }
    }

    // -------------------------------------------------------------------------------------

    /// Reads a value from the given position.
    /// Result is zero extended to 64-bit.
    fn raw_get_mem(&self, pos: u64, sizecode: u8) -> Result<u64, ExecError> {
        Ok(match sizecode {
            0 => self.get_mem_u8(pos)? as u64,
            1 => self.get_mem_u16(pos)? as u64,
            2 => self.get_mem_u32(pos)? as u64,
            3 => self.get_mem_u64(pos)?,
            _ => panic!(),
        })
    }
    /// Writes a value to the given position.
    /// If the value is too large, it is truncated.
    fn raw_set_mem(&mut self, pos: u64, sizecode: u8, val: u64) -> Result<(), ExecError> {
        match sizecode {
            0 => self.set_mem_u8(pos, val as u8),
            1 => self.set_mem_u16(pos, val as u16),
            2 => self.set_mem_u32(pos, val as u32),
            3 => self.set_mem_u64(pos, val),
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
        [ get_mem_adv_u8 : u8 => get_mem_u8 ],
        [ get_mem_adv_u16 : u16 => get_mem_u16 ],
        [ get_mem_adv_u32 : u32 => get_mem_u32 ],
        [ get_mem_adv_u64 : u64 => get_mem_u64 ],
    }

    /// Simultaneously advances and reads a value at the current instruction pointer position.
    /// The value is zero extended to 64-bit.
    fn raw_get_mem_adv(&mut self, sizecode: u8) -> Result<u64, ExecError> {
        let res = self.raw_get_mem(self.instruction_pointer as u64, sizecode)?;
        self.instruction_pointer += 1 << sizecode;
        Ok(res)
    }

    // -------------------------------------------------------------------------------------

    /// Advances and reads an address format from the current instruction pointer position.
    fn get_address_adv(&mut self) -> Result<u64, ExecError> {
        // [1: imm][1:][2: mult_1][2: size][1: r1][1: r2]   ([4: r1][4: r2])   ([size: imm])

        let settings = self.get_mem_adv_u8()?;
        let regs = if settings & 3 != 0 { self.get_mem_adv_u8()? } else { 0 };
        let sizecode = (settings >> 2) & 3;

        let mut res = if settings & 0x80 != 0 { self.raw_get_mem_adv(sizecode)? } else { 0 };
        if settings & 2 != 0 { res = res.wrapping_add(self.cpu_regs[regs as usize >> 4].raw_get(sizecode) << ((settings >> 4) & 3)); }
        if settings & 1 != 0 { res = res.wrapping_add(self.cpu_regs[regs as usize >> 4].raw_get(sizecode)); }

        Ok(res)
    }
}
impl Default for Emulator {
    fn default() -> Self {
        Emulator::new()
    }
}