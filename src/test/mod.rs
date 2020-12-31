use crate::common::serialization::*;
use crate::asm::*;

fn serialize_deserialize<T>(thing: &T) -> T where T: BinaryRead + BinaryWrite {
    let mut f = vec![];
    thing.bin_write(&mut f).unwrap();
    T::bin_read(&mut f.as_slice()).unwrap()
}

macro_rules! assemble_physical_file {
    ($name:literal) => {
        ($name.to_owned(), assemble($name, &mut include_str!(concat!("../asm/stdlib/", $name)).as_bytes(), Default::default()).unwrap())
    }
}
fn assemble_stdlib() -> Vec<(String, ObjectFile)> {
    vec![
        assemble_physical_file!("start.asm"),
        assemble_physical_file!("malloc.asm"),
        assemble_physical_file!("exit.asm"),
        assemble_physical_file!("ctype.asm"),
    ]
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
    (std $($asm:expr),*) => { asm_unwrap_link!([assemble_stdlib()] $($asm),* => Some(("start", "main"))) };
}
macro_rules! asm_unwrap_link_unwrap {
    ([$lib:expr] $($asm:expr),* => $entry:expr) => { serialize_deserialize(&asm_unwrap_link!([$lib] $($asm),* => $entry).unwrap()) };
    ($($asm:expr),*) => { serialize_deserialize(&asm_unwrap_link!($($asm),*).unwrap()) };
    (std $($asm:expr),*) => { serialize_deserialize(&asm_unwrap_link!(std $($asm),*).unwrap()) };
}

mod asm_error_tests;
mod lnk_error_tests;
mod exe_tests;
mod exe_syscall_tests;
mod stdlib_tests;