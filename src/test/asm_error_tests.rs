use super::*;
use crate::asm::{*, expr::ValueType};
use crate::asm::expr::*;

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
    if let Ok(_) = assemble("test.asm", &mut readable("\n#!csx -s".into()), Default::default()) {
        panic!();
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
            assert_eq!(e.pos, Some(0));
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
    match assemble("test.asm", &mut readable("  static_assert false".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertFailure));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(2));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("  static_assert abc".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::FailedCriticalExpression(_)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("  static_assert 1; hello".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::AssertArgNotLogical(ValueType::Integer)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("  static_assert;".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            assert!(matches!(e.kind, AsmErrorKind::ArgsExpectedCount(1)));
            assert_eq!(e.line_num, 1);
            assert_eq!(e.pos, Some(2));
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_global_uses_extern() {
    if let Err(e) = assemble("test.asm", &mut readable("extern abc\nval: equ abc".into()), Default::default()) {
        panic!("{:?}", e);
    }
    match assemble("test.asm", &mut readable("global val\nextern abc\nval: equ abc".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => {
            match e.kind {
                AsmErrorKind::GlobalUsesExtern { extern_sym } => {
                    assert_eq!(extern_sym, "abc");
                }
                _ => panic!("{:?}", e),
            }
            assert_eq!(e.line_num, 3);
            assert_eq!(e.pos, None);
            assert!(e.inner_err.is_none());
        }
    }
}

#[test]
fn test_double_global_extern() {
    match assemble("test.asm", &mut readable("global abc\nglobal abc".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("extern abc\nextern abc".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("global abc, abc".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("extern abc, abc".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nmov eax, [ah + al]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nmov eax, [al]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nmov eax, [byte 0]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [rax + rbx + rcx]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [dword bx]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [bx + rcx]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [2*rax + 2*rbx]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [6*rax]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [0*eax + 1*rax]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [1 / eax]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [eax >> 2]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [eax * eax]".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => { // TODO: at this point i'm not 100% sure what the error message should be - for now, just make sure this fails
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment text\nlea rax, [eax * ebx]".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => { // TODO: at this point i'm not 100% sure what the error message should be - for now, just make sure this fails
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment text\nlea rax, [ebx * eax]".into()), Default::default()) {
        Ok(_) => panic!(),
        Err(e) => { // TODO: at this point i'm not 100% sure what the error message should be - for now, just make sure this fails
            assert_eq!(e.line_num, 2);
            assert_eq!(e.pos, Some(9));
            assert!(e.inner_err.is_none());
        }
    }
    match assemble("test.asm", &mut readable("segment text\nlea rax, [2.0 * rax]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, []".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("segment text\nlea rax, [dword]".into()), Default::default()) {
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
    match assemble("test.asm", &mut readable("val: equ 1.0 + foo\nfoo: equ 2\n\n\n\n\n\n\n\n\n\n".into()), Default::default()) {
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