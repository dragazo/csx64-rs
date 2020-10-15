use std::io::Cursor;

mod asm_error_tests;

#[cfg(test)]
fn readable(s: String) -> Cursor<Vec<u8>> {
    Cursor::new(s.into_bytes())
}