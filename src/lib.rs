#![forbid(unsafe_code)]

//! CSX64 is effectively a cross-platform, custom 64-bit processor emulator featuring its own execution engine, machine code, assembly language, and linker.
//! It was originally intended to be an educational tool to teach assembly programming in a safe, well-defined, platform-independent framework.
//! This crate contains only the CSX64 library code (no application/cli).
//! 
//! # Example of Usage
//! 
//! ```
//! # use csx64::*;
//! // an example program just to show the assemble/link/execute process
//! let prog_name = "demo.asm";
//! let prog = r"
//!     global main
//! 
//!     segment text
//!     main:
//!         mov edi, 5
//!         mov esi, 4
//!         add edi, esi
//!         
//!         mov eax, edi
//!         ret
//! ";
//! 
//! // assemble the assembly program into an object file
//! let obj = match asm::assemble(prog_name, &mut prog.as_bytes(), Default::default()) {
//!     Ok(obj) => obj,
//!     Err(e) => panic!("{}", e), // assemble errors (above program has no errors)
//! };
//! 
//! // get a copy of the C standard library object files (implemented in CSX64 assembly)
//! let mut objs = asm::stdlib();
//! objs.push((String::from(prog_name), obj)); // add our object file(s) to the end
//! 
//! // link the object files into an executable - we want the starting point to be `main`
//! let exe = match asm::link(objs, Some(("start", "main"))) {
//!     Ok(exe) => exe,
//!     Err(e) => panic!("{}", e), // link errors (above program has no errors)
//! };
//! 
//! // create an emulator, load up the executable, and execute
//! let mut emu = exec::Emulator::new();
//! emu.init(&exe, &Default::default());
//! let (_, state) = emu.execute_cycles(u64::MAX);
//! assert_eq!(state, exec::StopReason::Terminated(9)); // should terminate with result 9
//! ```

#[macro_use] extern crate num_derive;
#[macro_use] extern crate lazy_static;

macro_rules! mask {
    ($src:ident : $($mask:ident)|+) => {
        $($src::$mask)|+
    };
    () => { 0 };
}

pub mod exec;
pub mod asm;
pub mod common;

#[cfg(test)]
mod test;
