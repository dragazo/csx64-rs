use std::io::Cursor;
use crate::common::serialization::*;

fn readable(s: String) -> Cursor<Vec<u8>> {
    Cursor::new(s.into_bytes())
}

fn serialize_deserialize<T>(thing: &T) -> T where T: BinaryRead + BinaryWrite {
    let mut f = Cursor::new(vec![]);
    thing.bin_write(&mut f).unwrap();
    f.set_position(0);
    T::bin_read(&mut f).unwrap()
}

macro_rules! asm_unwrap_link {
    ($($asm:expr),* => $entry:expr) => {{
        let src: Vec<String> = vec![$($asm),*];
        let mut input: Vec<(String, ObjectFile)> = Vec::with_capacity(src.len());
        for (i, src) in src.into_iter().enumerate() {
            let obj = assemble(&format!("file{}.asm", i), &mut readable(src), Default::default()).unwrap();
            input.push((format!("file{}.o", i), serialize_deserialize(&obj)));
        }
        link(input, $entry)
    }}
}
macro_rules! asm_unwrap_link_unwrap {
    ($($asm:expr),* => $entry:expr) => {{
        let exe = asm_unwrap_link!($($asm),* => $entry).unwrap();
        serialize_deserialize(&exe)
    }}
}

mod asm_error_tests;
mod lnk_error_tests;
mod exe_tests;