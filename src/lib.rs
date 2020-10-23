#![forbid(unsafe_code)]

//! An implementation of the CSX64 library in native, safe rust.
//! 
//! **Note: This crate is still in the initial phases of functionality, and does not yet have support for all instructions.**
//! 
//! CSX64 is effectively a cross-platform, custom 64-bit processor emulator featuring its own execution engine, machine code, assembly language, and linker.
//! It was originally intended to be an educational tool to teach assembly programming in a safe, well-defined, platform-independent framework.
//! 
//! This crate contains only the CSX64 library code.
//! A CLI driver program will be released as a separate GitHub project.
//! 
//! There are also [C#](https://github.com/dragazo/CSX64) and [C++](https://github.com/dragazo/CSX64-cpp) implementations of CSX64,
//! however they've largely been deprecated in favor of this implementation (eventually) and will likely not be up to date with the features present in this version.
//! Note that, while any CSX64 assembly program should work identically in any implementation (of the same version),
//! CSX64 object files and executables are not compatible across different implementations;
//! however, they are compatible across different platforms using the same implementation.

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