#![forbid(unsafe_code)]

//! An implementation of the CSX64 library in native, safe rust.
//! 
//! CSX64 is effectively a cross-platform, custom 64-bit processor emulator featuring its own execution engine, machine code, assembly language, and linker.
//! It was originally intended to be an educational tool to teach assembly programming in a safe, well-defined, platform-independent framework.
//! 
//! This crate contains only the CSX64 library code.
//! A CLI driver program will be released as a separate GitHub project.
//! 
//! There are also [C#](https://github.com/dragazo/CSX64) and [C++](https://github.com/dragazo/CSX64-cpp) implementations of CSX64.
//! Note that, while any CSX64 assembly program should work identically in any implementation,
//! CSX64 shared object files, object files, and executables are not compatible across different implementations.
//! However, they are compatible across different platforms using the same implementation.

#[macro_use] extern crate num_derive;
#[macro_use] extern crate lazy_static;
#[macro_use] extern crate bitflags;

pub mod exec;
pub mod asm;
pub mod common;