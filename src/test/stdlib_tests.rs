use std::iter;

use super::*;
use crate::exec::*;

#[test]
fn test_no_main() {
    let res = asm_unwrap_link!(std r"
    segment text
    main:
    hlt
    mov eax, 56
    ret
    ");
    match res {
        Ok(_) => panic!(),
        Err(e) => match e {
            LinkError::EntryPointTargetNotDefined => (),
            x => panic!("{:?}", x),
        }
    }
}

#[test]
fn test_stdlib_return() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    segment text
    main:
    hlt
    mov eax, 56
    ret
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(56));
}

macro_rules! test_ctype_return {
    ($e:ident, $true_range:expr, $false_range:expr) => {{
        for val in $true_range {
            $e.cpu.set_edi(val);
            assert_ne!($e.execute_cycles(u64::MAX).0, 0);
            if $e.cpu.get_eax() != 1 {
                panic!("failed {:#x}", val);
            }
        }
        for val in $false_range {
            $e.cpu.set_edi(val);
            assert_ne!($e.execute_cycles(u64::MAX).0, 0);
            if $e.cpu.get_eax() != 0 {
                panic!("failed {:#x}", val);
            }
        }
    }}
}

#[test]
fn test_iscntrl() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern iscntrl
    segment text
    main:
    hlt
    call iscntrl
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = (0x00..=0x1f).chain(iter::once(0x7f));
    let false_range = 0x20..=0x7e;
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isblank() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isblank
    segment text
    main:
    hlt
    call isblank
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = [0x09, 0x20].iter().copied();
    let false_range = (0x00..=0x08).chain(0x0a..=0x1f).chain(0x21..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isspace() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isspace
    segment text
    main:
    hlt
    call isspace
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = (0x09..=0x0d).chain(iter::once(0x20));
    let false_range = (0x00..=0x08).chain(0x0e..=0x1f).chain(0x21..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isupper() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isupper
    segment text
    main:
    hlt
    call isupper
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = 0x41..=0x5a;
    let false_range = (0x00..=0x40).chain(0x5b..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_islower() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern islower
    segment text
    main:
    hlt
    call islower
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = 0x61..=0x7a;
    let false_range = (0x00..=0x60).chain(0x7b..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isalpha() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isalpha
    segment text
    main:
    hlt
    call isalpha
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = (0x41..=0x5a).chain(0x61..=0x7a);
    let false_range = (0x00..=0x40).chain(0x5b..=0x60).chain(0x7b..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isdigit() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isdigit
    segment text
    main:
    hlt
    call isdigit
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = 0x30..=0x39;
    let false_range = (0x00..=0x2f).chain(0x3a..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isxdigit() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isxdigit
    segment text
    main:
    hlt
    call isxdigit
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = (0x30..=0x39).chain(0x41..=0x46).chain(0x61..=0x66);
    let false_range = (0x00..=0x2f).chain(0x3a..=0x40).chain(0x47..=0x60).chain(0x67..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isalnum() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isalnum
    segment text
    main:
    hlt
    call isalnum
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = (0x30..=0x39).chain(0x41..=0x5a).chain(0x61..=0x7a);
    let false_range = (0x00..=0x2f).chain(0x3a..=0x40).chain(0x5b..=0x60).chain(0x7b..=0x7f);
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_ispunct() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern ispunct
    segment text
    main:
    hlt
    call ispunct
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = (0x21..=0x2f).chain(0x3a..=0x40).chain(0x5b..=0x60).chain(0x7b..=0x7e);
    let false_range = (0x00..=0x20).chain(0x30..=0x39).chain(0x41..=0x5a).chain(0x61..=0x7a).chain(iter::once(0x7f));
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isgraph() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isgraph
    segment text
    main:
    hlt
    call isgraph
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = 0x21..=0x7e;
    let false_range = (0x00..=0x20).chain(iter::once(0x7f));
    test_ctype_return!(e, true_range, false_range);
}
#[test]
fn test_isprint() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern isprint
    segment text
    main:
    hlt
    call isprint
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    let true_range = 0x20..=0x7e;
    let false_range = (0x00..=0x1f).chain(iter::once(0x7f));
    test_ctype_return!(e, true_range, false_range);
}

#[test]
fn test_tolower() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern tolower
    segment text
    main:
    hlt
    call tolower
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    for ch in 0x00..=0x7f {
        e.cpu.set_edi(ch);
        assert_ne!(e.execute_cycles(u64::MAX).0, 0);
        let res = e.cpu.get_eax();
        if res != std::char::from_u32(ch).unwrap().to_ascii_lowercase() as u32 {
            panic!("failed tolower: {:#x} -> {:#x}", ch, res);
        }
    }
}
#[test]
fn test_toupper() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern toupper
    segment text
    main:
    hlt
    call toupper
    jmp main
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_ne!(e.execute_cycles(u64::MAX).0, 0);
    assert_eq!(e.get_state(), State::Running);

    for ch in 0x00..=0x7f {
        e.cpu.set_edi(ch);
        assert_ne!(e.execute_cycles(u64::MAX).0, 0);
        let res = e.cpu.get_eax();
        if res != std::char::from_u32(ch).unwrap().to_ascii_uppercase() as u32 {
            panic!("failed tolower: {:#x} -> {:#x}", ch, res);
        }
    }
}