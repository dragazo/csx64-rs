use super::*;
use crate::asm::{*, expr::ValueType};

#[test]
fn test_empty_source() {
    if let Err(e) = assemble("test.asm", &mut readable("".into()), Default::default()) {
        panic!("{:?}", e);
    }
}

#[test]
fn test_shebang() {
    if let Err(e) = assemble("test.asm", &mut readable("#!csx -s".into()), Default::default()) {
        panic!("{:?}", e);
    }
}

#[test]
fn test_segment() {
    if let Err(e) = assemble("test.asm", &mut readable("segMent tExT".into()), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut readable("segment eegrf".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExpectedSegment));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment text dsdef".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExtraContentAfterArgs));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(13));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment text, dsdef".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(1)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment tExT\nsegment text".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::SegmentAlreadyCompleted));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    if let Err(e) = assemble("test.asm", &mut readable("segment tExT\nsegment data\nsegment rodata\nsegment bss".into()), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut readable("segment tExT\nlabel: segment data".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::LabelOnSegmentLine));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_ins_outside_text_seg() {
    match assemble("test.asm", &mut readable("mov eax, 0".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment data\nmov eax, 0".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment rodata\nmov eax, 0".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment bss\nmov eax, 0".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_no_arg_ops() {
    if let Err(e) = assemble("test.asm", &mut readable("segment text\nnop".into()), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut readable("segment text\nnop 0".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(0)));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_binary_ops() {
    if let Err(e) = assemble("test.asm", &mut readable("segment text\nmov rax, 0".into()), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut readable("segment text\n   mov rax, 0 0".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExtraContentAfterArgs));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(14));
            assert!(e.inner_err.is_none());
        }
    }
    if let Err(e) = assemble("test.asm", &mut readable("segment text\n   mov rax,0;0".into()), Default::default()) {
        panic!("{:?}", e);
    }
}

#[test]
fn test_assert() {
    if let Err(e) = assemble("test.asm", &mut readable("static_assert true".into()), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut readable("static_assert qword true".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertArgHadSizeSpec));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("static_assert false".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertFailure));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("static_assert abc".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            println!("{:?}", e);
            assert!(matches!(e.kind, AsmErrorKind::FailedCriticalExpression(_)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("static_assert 1; hello".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            println!("{:?}", e);
            assert!(matches!(e.kind, AsmErrorKind::AssertArgNotLogical(ValueType::Signed)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("static_assert;".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            println!("{:?}", e);
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(1)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}