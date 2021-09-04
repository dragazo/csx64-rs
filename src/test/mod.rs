use crate::common::serialization::*;
use crate::asm::*;
use crate::exec::*;
use crate::exec::fs::*;

use std::io::Cursor;
use std::sync::{Arc, Mutex};

fn serialize_deserialize<T>(thing: &T) -> T where T: BinaryRead + BinaryWrite {
    let mut f = vec![];
    thing.bin_write(&mut f).unwrap();
    T::bin_read(&mut f.as_slice()).unwrap()
}

macro_rules! asm_unwrap_link {
    ([$lib:expr] $($asm:expr),* => $entry:expr) => {{
        let src: Vec<&str> = vec![$($asm),*];
        let mut input: Vec<(String, ObjectFile)> = $lib;
        for (i, src) in src.into_iter().enumerate() {
            let obj = assemble(&format!("file{}.asm", i), &mut src.as_bytes(), Default::default()).unwrap();
            input.push((format!("file{}.o", i), serialize_deserialize(&obj)));
        }
        link(input, $entry)
    }};
    ($($asm:expr),*) => { asm_unwrap_link!([vec![]] $($asm),* => None) };
    (std $($asm:expr),*) => { asm_unwrap_link!([stdlib()] $($asm),* => Some(("start", "main"))) };
}
macro_rules! asm_unwrap_link_unwrap {
    ([$lib:expr] $($asm:expr),* => $entry:expr) => { serialize_deserialize(&asm_unwrap_link!([$lib] $($asm),* => $entry).unwrap()) };
    ($($asm:expr),*) => { serialize_deserialize(&asm_unwrap_link!($($asm),*).unwrap()) };
    (std $($asm:expr),*) => { serialize_deserialize(&asm_unwrap_link!(std $($asm),*).unwrap()) };
}

fn setup_standard_memory_streams(e: &mut Emulator) -> (Arc<Mutex<MemoryFile>>, Arc<Mutex<MemoryFile>>, Arc<Mutex<MemoryFile>>) {
    let stdin = Arc::new(Mutex::new(MemoryFile { content: Cursor::new(vec![]), readable: true, writable: false, seekable: false, appendonly: false, interactive: true }));
    let stdout = Arc::new(Mutex::new(MemoryFile { content: Cursor::new(vec![]), readable: false, writable: true, seekable: false, appendonly: false, interactive: false }));
    let stderr = Arc::new(Mutex::new(MemoryFile { content: Cursor::new(vec![]), readable: false, writable: true, seekable: false, appendonly: false, interactive: false }));
    e.files.handles[0] = Some(stdin.clone());
    e.files.handles[1] = Some(stdout.clone());
    e.files.handles[2] = Some(stderr.clone());
    (stdin, stdout, stderr)
}

mod asm_error_tests;
mod lnk_error_tests;
mod exe_tests;
mod exe_syscall_tests;
mod stdlib_tests;
mod stdio_tests;