use super::*;

#[test]
fn test_empty() {
    match asm_unwrap_link!([vec![]] => None) {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
    match asm_unwrap_link!([vec![]] => Some(("start", "main"))) {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
}