use super::*;
use crate::asm::*;

#[test]
fn test_empty() {
    match assemble_and_link!(; None) {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
    match assemble_and_link!(; Some(("start", "main"))) {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
}