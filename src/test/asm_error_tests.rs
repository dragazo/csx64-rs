use crate::asm::{*, expr::ValueType};
use crate::asm::expr::*;

#[test]
fn test_empty_source() {
    if let Err(e) = assemble("test.asm", &mut "".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
}

#[test]
fn test_shebang() {
    if let Err(e) = assemble("test.asm", &mut "#!csx -s".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
    if let Ok(_) = assemble("test.asm", &mut "\n#!csx -s".as_bytes(), Default::default()) {
        panic!();
    }
}

#[test]
fn test_segment() {
    if let Err(e) = assemble("test.asm", &mut "segMent tExT".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut "segment eegrf".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExpectedSegment));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text dsdef".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExtraContentAfterArgs));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(13));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text, dsdef".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(&[1])));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(0));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment tExT\nsegment text".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::SegmentAlreadyCompleted));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    if let Err(e) = assemble("test.asm", &mut "segment tExT\nsegment data\nsegment rodata\nsegment bss".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut "segment tExT\nlabel: segment data".as_bytes(), Default::default()) {
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
    match assemble("test.asm", &mut "mov eax, 0".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment data\nmov eax, 0".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment rodata\nmov eax, 0".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::InstructionOutsideOfTextSegment));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment bss\nmov eax, 0".as_bytes(), Default::default()) {
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
    if let Err(e) = assemble("test.asm", &mut "segment text\nnop".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut "segment text\nnop 0".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(&[0])));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_binary_ops() {
    if let Err(e) = assemble("test.asm", &mut "segment text\nmov rax, 0".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut "segment text\n   mov rax, 0 0".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ExtraContentAfterArgs));
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(14));
            assert!(e.inner_err.is_none());
        }
    }
    if let Err(e) = assemble("test.asm", &mut "segment text\n   mov rax,0;0".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
}

#[test]
fn test_assert() {
    if let Err(e) = assemble("test.asm", &mut "static_assert true".as_bytes(), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut "static_assert qword true".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertArgHadSizeSpec));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "  static_assert false".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertFailure));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(2));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "  static_assert abc".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::FailedCriticalExpression(_)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "  static_assert 1; hello".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertArgNotLogical(ValueType::Integer)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "  static_assert;".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(&[1])));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(2));
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_double_global_extern() {
    match assemble("test.asm", &mut "global abc\nglobal abc".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num } => assert_eq!(prev_line_num, 1),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "extern abc\nextern abc".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num } => assert_eq!(prev_line_num, 1),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "global abc, abc".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num } => assert_eq!(prev_line_num, 1),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "extern abc, abc".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::RedundantGlobalOrExternDecl { prev_line_num } => assert_eq!(prev_line_num, 1),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_addr_8bit() {
    match assemble("test.asm", &mut "segment text\nmov eax, [ah + al]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::SizeUnsupported) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nmov eax, [al]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::SizeUnsupported) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nmov eax, [byte 0]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::SizeUnsupported) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_bad_addr() {
    match assemble("test.asm", &mut "segment text\nlea rax, [rax + rbx + rcx]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::InvalidRegMults) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [dword bx]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::ConflictingSizes) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [bx + rcx]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::ConflictingSizes) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [2*rax + 2*rbx]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::InvalidRegMults) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [6*rax]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::InvalidRegMults) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [0*eax + 1*rax]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::ConflictingSizes) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [1 / eax]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::RegIllegalOp) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [eax >> 2]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::RegIllegalOp) => (),
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [eax * eax]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => { // TODO: at this point i'm not 100% sure what the error message should be - for now, just make sure this fails
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [eax * ebx]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => { // TODO: at this point i'm not 100% sure what the error message should be - for now, just make sure this fails
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [ebx * eax]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => { // TODO: at this point i'm not 100% sure what the error message should be - for now, just make sure this fails
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [2.0 * rax]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::RegMultNotCriticalExpr(reason)) => match reason {
                    EvalError::Illegal(IllegalReason::IncompatibleTypes(OP::Mul, ValueType::Float, ValueType::Integer)) => (),
                    _ => panic!("{:?}", reason),
                }
                _ => panic!("{:?}", e.kind),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, []".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::BadBase) => (),
                _ => panic!("{:?}", e.kind),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            let inner = *e.inner_err.unwrap();
            match inner.kind {
                AsmErrorKind::ExpectedExprTerm => (),
                _ => panic!("{:?}", inner.kind),
            }
            assert_eq!(inner.line_num, 2);
            assert_eq!(inner.pos, Some(10));
            assert!(inner.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nlea rax, [dword]".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::BadAddress(BadAddress::BadBase) => (),
                _ => panic!("{:?}", e.kind),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            let inner = *e.inner_err.unwrap();
            match inner.kind {
                AsmErrorKind::ExpectedExprTerm => (),
                _ => panic!("{:?}", inner.kind),
            }
            assert_eq!(inner.line_num, 2);
            assert_eq!(inner.pos, Some(15));
            assert!(inner.inner_err.is_none());
        }
    }
}

#[test]
fn test_late_expr_errors() {
    match assemble("test.asm", &mut "val: equ 1.0 + foo\nfoo: equ 2\n\n\n\n\n\n\n\n\n\n".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::ExprIllegalError(IllegalReason::IncompatibleTypes(OP::Add, ValueType::Float, ValueType::Integer)) => (),
                k => panic!("{:?}", k),
            }
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_value_unknown_size() {
    match assemble("test.asm", &mut "segment text\npush 5".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::CouldNotDeduceOperandSize => (),
                k => panic!("{:?}", k),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nmul 5".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::CouldNotDeduceOperandSize => (),
                k => panic!("{:?}", k),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut "segment text\nimul 5".as_bytes(), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::CouldNotDeduceOperandSize => (),
                k => panic!("{:?}", k),
            }
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}
