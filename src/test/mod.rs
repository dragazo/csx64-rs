use std::io::Cursor;

#[cfg(test)]
fn readable(s: String) -> Cursor<Vec<u8>> {
    Cursor::new(s.into_bytes())
}

macro_rules! assemble_and_link {
    ($($asm:expr),* => $entry:expr) => {{
        let src: Vec<String> = vec![$($asm),*];
        let mut input: Vec<(String, ObjectFile)> = Vec::with_capacity(src.len());
        for (i, src) in src.into_iter().enumerate() {
            input.push((format!("file{}.o", i), assemble(&format!("file{}.asm", i), &mut readable(src), Default::default()).unwrap()));
        }
        link(input, $entry)
    }}
}

mod asm_error_tests;
mod lnk_error_tests;
mod exe_tests;