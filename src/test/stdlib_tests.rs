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

const MALLOC_ALIGN: u64 = 16;

fn align_to(val: u64, align: u64) -> u64 {
    assert!(align.is_power_of_two());
    val + (val.wrapping_neg() & (align - 1))
}

struct MallocEntry {
    pos: u64,
    in_use: bool,
    next: u64,
    prev: u64,
}
fn get_malloc_walk(mem: &Memory, beg_ptr: u64, end_ptr: u64) -> Vec<(bool, u64)> {
    let beg = mem.get_u64(beg_ptr).unwrap();
    let end = mem.get_u64(end_ptr).unwrap();
    let mut res = vec![];
    
    let mut pos = beg;
    while pos != end {
        let meta_next = mem.get_u64(pos).unwrap();
        let in_use = meta_next & 1 != 0;
        let next = meta_next & !1;
        let prev = mem.get_u64(pos + 8).unwrap();
        res.push(MallocEntry { pos, in_use, next, prev });

        if next <= pos + 16 { panic!("pos: {:#x}, next: {:#x}", pos, next); }
        assert!(next - pos - 16 > 0);
        assert_eq!((pos + 16) % MALLOC_ALIGN, 0);

        pos = next;
    }

    if !res.is_empty() {
        assert_eq!(res.first().unwrap().prev, 0);
        assert_eq!(res.last().unwrap().next, end);
        for w in res.windows(2) {
            assert_eq!(w[0].next, w[1].pos);
            assert_eq!(w[1].prev, w[0].pos);
            assert!(w[0].in_use || w[1].in_use);
        }
    }

    res.iter().map(|x| (x.in_use, x.next - x.pos - 16)).collect()
}

#[test]
fn test_malloc() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern malloc, free
    extern __malloc_beg, __malloc_end
    segment text
    main:
    mov rax, __malloc_beg
    mov rbx, __malloc_end
    hlt

    mov edi, 22
    call malloc
    hlt
    mov rdi, rax
    call free
    hlt
    mov edi, 550
    call malloc
    hlt
    mov rdi, rax
    call free
    hlt
    mov edi, 44
    call malloc
    mov r15, rax ; 44 bytes
    hlt

    mov edi, 33
    call malloc
    mov r14, rax ; 33 bytes
    hlt

    mov rdi, r15
    call free
    hlt
    mov edi, 5
    call malloc
    mov r15, rax ; 5 bytes (previously 44)
    hlt
    mov edi, 7
    call malloc
    mov r13, rax ; 7 bytes
    hlt

    mov edi, 44
    call malloc
    hlt 
    mov rdi, rax
    call free
    hlt
    mov rdi, r15
    call free
    hlt
    mov edi, 48
    call malloc
    hlt
    mov rdi, rax
    call free
    hlt
    mov rdi, r13
    call free
    hlt
    mov edi, 44
    call malloc
    mov r15, rax
    hlt

    mov rdi, r14
    call free
    hlt
    mov rdi, r15
    call free ; at this point we've deallocated everything we allocated
    hlt
    
    mov edi, 256
    call malloc
    mov r15, rax
    hlt
    mov edi, 256
    call malloc
    mov r14, rax
    hlt
    mov edi, 256
    call malloc
    mov r13, rax
    hlt

    mov edi, 4096
    call malloc
    mov r12, rax
    hlt
    mov rdi, r15
    call free
    hlt
    mov rdi, r13
    call free
    hlt
    mov edi, 256*3
    call malloc
    hlt
    mov rdi, rax
    call free
    hlt

    mov rdi, r14
    call free ; this forces simultaneous left and right merge of the 3 256-byte allocation blocks
    hlt
    mov edi, 256*3
    call malloc
    hlt
    mov rdi, rax
    call free
    hlt
    mov rdi, r12
    call free ; we've again deallocated everything
    hlt
    mov edi, 10001
    call malloc
    hlt
    mov rdi, rax
    call free ; nothing allocated
    hlt

    mov edi, 0
    call malloc
    hlt
    mov edi, 0
    call free
    hlt

    mov eax, 77
    ret
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let base = e.cpu.get_rbp();
    assert_eq!(base, e.memory.len() as u64);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let beg_ptr = e.cpu.get_rax();
    let end_ptr = e.cpu.get_rbx();
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let first = e.cpu.get_rax();
    assert!(first >= base);
    assert_eq!(first % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 32)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 32)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 560)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 560)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48), (false, 496)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let second = e.cpu.get_rax();
    assert!(first + 44 <= second);
    assert_eq!(first % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48), (true, 48), (false, 432)]);
    
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 48), (true, 48), (false, 432)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (false, 16), (true, 48), (false, 432)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let third = e.cpu.get_rax();
    assert!(first + 5 <= third);
    assert!(third + 7 <= second);
    assert_eq!(third % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (true, 16), (true, 48), (false, 432)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let fourth = e.cpu.get_rax();
    assert!(second + 33 <= fourth);
    assert_eq!(fourth % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (true, 16), (true, 48), (true, 48), (false, 368)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (true, 16), (true, 48), (false, 432)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 16), (true, 16), (true, 48), (false, 432)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), fourth);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 16), (true, 16), (true, 48), (true, 48), (false, 368)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 16), (true, 16), (true, 48), (false, 432)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 48), (true, 48), (false, 432)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48), (true, 48), (false, 432)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48), (false, 496)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 560)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256), (false, 288)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256), (true, 256), (false, 16)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256), (true, 256), (true, 256)]);

    let new1 = e.cpu.get_r15();
    let new2 = e.cpu.get_r14();
    let new3 = e.cpu.get_r13();
    assert_eq!(new1, first);
    assert!(new1 + 256 <= new2);
    assert!(new2 + 256 <= new3);
    assert_eq!(new2 % MALLOC_ALIGN, 0);
    assert_eq!(new3 % MALLOC_ALIGN, 0);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let big = e.cpu.get_rax();
    assert!(new3 + 256 <= big);
    assert_eq!(big % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256), (true, 256), (true, 256), (true, 4096)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 256), (true, 256), (true, 256), (true, 4096)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 256), (true, 256), (false, 256), (true, 4096)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let fin = e.cpu.get_rax();
    assert!(big + 4096 <= fin);
    assert_eq!(fin % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 256), (true, 256), (false, 256), (true, 4096), (true, 768)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 256), (true, 256), (false, 256), (true, 4096), (false, 768)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 800), (true, 4096), (false, 768)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert!(e.cpu.get_rax() + 256 * 3 <= big);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 768), (false, 16), (true, 4096), (false, 768)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 800), (true, 4096), (false, 768)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 5696)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 10016)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 10016)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 10016)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 10016)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(77));
}
