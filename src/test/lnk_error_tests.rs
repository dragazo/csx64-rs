use super::*;
use super::expr::*;

#[test]
fn test_empty() {
    match asm_unwrap_link!([vec![]] => None) {
        Ok(_) => panic!(),
        Err(e) => match e.kind {
            LinkErrorKind::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
    match asm_unwrap_link!([vec![]] => Some(("start", "main"))) {
        Ok(_) => panic!(),
        Err(e) => match e.kind {
            LinkErrorKind::NothingToLink => (),
            _ => panic!("{:?}", e),
        }
    }
}
#[test]
fn test_cyclic_deps() {
    if let Err(e) = asm_unwrap_link!("global a\nextern b\na: equ b", "global b\nextern a\nb: equ 6") {
        panic!("{:?}", e);
    }
    match asm_unwrap_link!("global a\nextern b\na: equ b", "global b\nextern a\nb: equ a") {
        Ok(_) => panic!(),
        Err(e) => match e.kind {
            LinkErrorKind::EvalFailure { src: _, line_num: 3, reason: EvalError::Illegal(IllegalReason::CyclicDependency) } => (),
            _ => panic!("{:?}", e),
        }
    }
    match asm_unwrap_link!("global a\nextern b\na: equ b", "global b\nextern a\nb: equ 1+a+1") {
        Ok(_) => panic!(),
        Err(e) => match e.kind {
            LinkErrorKind::EvalFailure { src: _, line_num: 3, reason: EvalError::Illegal(IllegalReason::CyclicDependency) } => (),
            _ => panic!("{:?}", e),
        }
    }
    match asm_unwrap_link!("global a\nextern b\na: equ b+1", "global b\nextern a\nb: equ a") {
        Ok(_) => panic!(),
        Err(e) => match e.kind {
            LinkErrorKind::EvalFailure { src: _, line_num: 3, reason: EvalError::Illegal(IllegalReason::CyclicDependency) } => (),
            _ => panic!("{:?}", e),
        }
    }
}