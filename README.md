# CSX64

An implementation of the CSX64 library in native, safe rust.

CSX64 is effectively a cross-platform, custom 64-bit processor emulator featuring its own execution engine, machine code, assembly language, and linker.
It was originally intended to be an educational tool to teach assembly programming in a safe, well-defined, platform-independent framework.

This crate contains only the CSX64 library code, enabling programatic access to the assembler and linker.
A CLI driver program will be released as a separate GitHub project.

There are also [C#](https://github.com/dragazo/CSX64) and [C++](https://github.com/dragazo/CSX64-cpp) implementations of CSX64.
Note that, while any CSX64 assembly program should work identically in any implementation,
CSX64 shared object files, object files, and executables are not compatible across different implementations.
However, they are compatible across different platforms using the same implementation.

This (rust) implementation is far from operational, but is intended to become the official implementation once completed due to rust's safety guarantees and convenience of testing.
In the meantime, the current official implementation is the C++ one.

For more information, consult the documentation via `cargo doc`.