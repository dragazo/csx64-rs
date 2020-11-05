use super::*;
use crate::asm::*;

#[test]
fn test_empty() {
    match asm_unwrap_link!(=> None) {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
    match asm_unwrap_link!(=> Some(("start", "main"))) {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
}