use std::iter;
use rand::prelude::*;

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
    val + (val.wrapping_neg() & (align - 1))
}

struct MallocEntry {
    pos: u64,
    in_use: bool,
    next: u64,
    prev: u64,
}
impl std::fmt::Debug for MallocEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", (self.in_use, self.next.wrapping_sub(self.pos).wrapping_sub(16)))
    }
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

        if next < pos + 16 { panic!("pos: {:#x}, next: {:#x} --- partial: {:?}", pos, next, res); }
        let len = next - pos - 16;
        assert_eq!((pos + 16) % MALLOC_ALIGN, 0); // make sure allocation is aligned
        assert_eq!(mem.get(pos + 16, len).unwrap().len() as u64, len); // make sure allocation is within mem bounds
        assert!(len != 0 || !in_use); // len = 0 -> !in_use

        pos = next;
    }

    if !res.is_empty() {
        assert_eq!(res.first().unwrap().prev, 0); // make sure prev root is null
        assert_eq!(res.last().unwrap().next, end); // make sure next root is the end pointer
        assert_eq!(res.last().unwrap().in_use, true); // last block should be occupied (vacant tails are pruned)
        for w in res.windows(2) {
            assert_eq!(w[0].next, w[1].pos); // make sure the double-links are sound
            assert_eq!(w[1].prev, w[0].pos);
            assert!(w[0].in_use || w[1].in_use); // make sure we don't have adjacent unallocated buckets (should have been merged)
        }
    }

    res.iter().map(|x| (x.in_use, x.next - x.pos - 16)).collect()
}

const LONG_MESSAGE: &'static [u8] = r"
if i could have one last wish,
i would wish for a tasty fish.
harry potter and the application of fourier transforms for gausian blurring.
bakusquad needs to be explored more in canon - who even cares about deku or the bean bag chair we call shouto?
long miscelanous text trying to add content to the thing so i can see if the allocation functions are copying things right.
vscode is doing this cute thing where it tries to give me code completion when i'm typing strings.
so when i put a period and press enter it just inserts whatever it thinks is most appropriate for a string.
let's face it, the ending of voltron was stupid and had so much potential prior to the final season.
doesn't even make any sense that alura and lance would hook up in the end anyway.
if anything it was looking like lance and keith were going to have a thing.
but at the very least don't suddenly pair keith with that one random alien chick we know... god damn the writers are dumb.
it's like they needed every character to be in a relationship at the end (even shiro, but in the worst way possible).
like, ya, that's a great way to spend the last half of the final season...
surprisingly, this isn't quite long enough yet, so imma just put a bunch of random stuff now...
쥎흐바위히붛느싀욶르베쇠루호싫스브흐르그쇰벩츠쇠엫뢰셉르획셈르흐그최엫그르시,츄엟브쇼엫르쇠멯브르고시,에획르스허임르흐브네숋르므비세,뢰잋
세이뤁스블체롄트리화8읕축뤼차웨부헤잍룬휘웨괯궄뤼콥르귴느루개우우게율추급궤웉부웨일뷰아웨이유붸튜웇게가웋젤나우체가우붸이뤁쀅차위눽새우그우라유 붹래우툰브체유아
아웨읿나우베유우휴엧그나우위게류우규네뤄읕느고위우겣튜귀우겔쥬우게이투궤유투윁치무욳그뉴아웅에유타누거웉규웨곰트춰윿그트매우웽튜우게 튜에퉃과외윽므즈타웉.
ok, considering this is in utf8, that should be plenty of bytes by now.
well, it's been fun, but i really must be going.
see you in the next release!
".as_bytes();

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
    assert_eq!(first, align_to(base, MALLOC_ALIGN) + 16);
    assert_eq!(first % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 32)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 560)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let second = e.cpu.get_rax();
    assert!(first + 44 <= second);
    assert_eq!(first % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48), (true, 48)]);
    
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 48), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (false, 16), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let third = e.cpu.get_rax();
    assert!(first + 5 <= third);
    assert!(third + 7 <= second);
    assert_eq!(third % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (true, 16), (true, 48)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let fourth = e.cpu.get_rax();
    assert!(second + 33 <= fourth);
    assert_eq!(fourth % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (true, 16), (true, 48), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16), (true, 16), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 16), (true, 16), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), fourth);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 16), (true, 16), (true, 48), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 16), (true, 16), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 48), (true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48), (true, 48)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 48)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256), (true, 256)]);
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
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 256), (true, 256), (false, 256), (true, 4096)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 800), (true, 4096)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert!(e.cpu.get_rax() + 256 * 3 <= big);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 768), (false, 16), (true, 4096)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 800), (true, 4096)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 10016)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(77));
}
#[test]
fn test_malloc_realloc() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern realloc
    extern __malloc_beg, __malloc_end
    segment text
    main:
    mov rax, __malloc_beg
    mov rbx, __malloc_end
    hlt

    mov edi, 0
    mov esi, 10
    call realloc
    hlt
    mov rdi, rax
    mov esi, 0
    call realloc
    hlt

    mov edi, 0
    mov esi, 20
    call realloc
    mov qword ptr [rax], 0xdeadbeefdeadbeef
    hlt
    mov rdi, rax
    mov esi, 64
    call realloc
    hlt
    mov rdi, rax
    mov esi, 24
    call realloc
    hlt
    mov rdi, rax
    mov esi, 250
    call realloc
    hlt
    mov rdi, rax
    mov esi, 32
    call realloc
    hlt
    mov rdi, rax
    mov esi, 64
    call realloc
    mov r15, rax
    hlt

    mov edi, null
    mov esi, 64
    call realloc
    mov r14, rax
    hlt
    mov edi, null
    mov esi, 64
    call realloc
    mov r13, rax
    hlt
    mov rdi, r14
    mov esi, 0
    call realloc
    hlt
    mov rdi, r15
    mov esi, 144
    call realloc
    hlt
    mov rdi, rax
    mov esi, 64
    call realloc
    hlt
    mov rdi, rax
    mov esi, 128
    call realloc
    hlt
    mov rdi, rax
    mov esi, 112
    call realloc
    hlt
    mov rdi, rax
    mov esi, 96
    call realloc
    hlt
    mov rdi, rax
    mov esi, 128
    call realloc
    hlt
    mov rdi, rax
    mov esi, 144
    call realloc
    hlt

    mov rdi, rax
    mov esi, 112
    call realloc
    hlt
    mov rdi, rax
    mov esi, 200
    call realloc
    mov r15, rax
    hlt
    mov edi, null
    mov esi, 128
    call realloc
    mov r14, rax
    hlt
    mov edi, 0
    mov esi, 0
    call realloc
    hlt
    mov edi, 0
    mov esi, 1
    call realloc
    mov r12, rax
    hlt
    mov rdi, r15
    mov esi, 191
    call realloc
    hlt
    mov rdi, r12
    mov esi, 0
    call realloc
    hlt
    mov rdi, r13
    mov esi, 48
    call realloc
    hlt
    mov rdi, r13
    mov esi, 0
    call realloc
    hlt
    mov rdi, r14
    mov esi, 0
    call realloc
    hlt

    mov edi, 0
    mov esi, 209
    call realloc
    hlt
    mov rdi, rax
    mov esi, 0
    call realloc
    hlt
    mov edi, 0
    mov esi, 208
    call realloc
    hlt
    mov rdi, rax
    mov esi, 0
    call realloc
    hlt
    mov edi, 0
    mov esi, 225
    call realloc
    mov r14, rax
    hlt
    mov rdi, r15
    mov esi, 224
    call realloc
    mov r13, rax
    hlt
    mov edi, null
    mov esi, 192
    call realloc
    hlt
    mov rdi, r13
    mov esi, 0
    call realloc
    hlt
    mov rdi, r15
    mov esi, 208
    call realloc
    hlt
    
    mov rdi, rax
    mov esi, 0
    call realloc
    hlt
    mov rdi, r14
    mov esi, 0
    call realloc
    hlt ; we've now deallocated everything we allocated

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
    assert_eq!(first, align_to(base, MALLOC_ALIGN) + 16);
    assert_eq!(first % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 16)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 32)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 32)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 256)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 32)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 64)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let second = e.cpu.get_rax();
    assert_eq!(second, first + 64 + 16);
    assert_eq!(second % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 64), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let third = e.cpu.get_rax();
    assert_eq!(third, second + 64 + 16);
    assert_eq!(third % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 64), (true, 64), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 64), (false, 64), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 144), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 64), (false, 64), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 112), (false, 16), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 96), (false, 32), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 144), (true, 64)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    e.memory.get_mut(first, 112).unwrap().clone_from_slice(&LONG_MESSAGE[300..300+112]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 112), (false, 16), (true, 64)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let mut fourth = e.cpu.get_rax();
    assert_eq!(fourth, third + 64 + 16);
    assert_eq!(fourth % MALLOC_ALIGN, 0);
    assert_eq!(e.memory.get(fourth, 112).unwrap(), &LONG_MESSAGE[300..300+112]);
    e.memory.get_mut(fourth, 200).unwrap().clone_from_slice(&LONG_MESSAGE[150..150+200]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 144), (true, 64), (true, 208)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    e.memory.get_mut(first, 128).unwrap().clone_from_slice(&LONG_MESSAGE[400..400+128]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64), (true, 208)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64), (true, 208)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let next = e.cpu.get_rax();
    assert_eq!(next, fourth + 208 + 16);
    assert_eq!(next % MALLOC_ALIGN, 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64), (true, 208), (true, 16)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), fourth);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64), (true, 192), (false, 0), (true, 16)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 64), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), third);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 0), (true, 48), (false, 0), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 128), (false, 80), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 224), (true, 192)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 224), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 224), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 208), (false, 0), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 224), (true, 192)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), next - 16);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 224), (true, 192), (true, 240)]);
    assert_eq!(e.memory.get(fourth, 192).unwrap(), &LONG_MESSAGE[150..150+192]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 224), (false, 192), (true, 240)]);
    assert_eq!(e.memory.get(first, 192).unwrap(), &LONG_MESSAGE[150..150+192]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first + 224 + 16);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 224), (true, 192), (true, 240)]);
    assert_eq!(e.memory.get(first, 192).unwrap(), &LONG_MESSAGE[150..150+192]);
    e.memory.get_mut(first + 224 + 16, 192).unwrap().copy_from_slice(&LONG_MESSAGE[700..700+192]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 224), (true, 192), (true, 240)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 208), (false, 208), (true, 240)]);
    assert_eq!(e.memory.get(first, 192).unwrap(), &LONG_MESSAGE[700..700+192]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 432), (true, 240)]);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(77));
}
#[test]
fn test_malloc_calloc() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern calloc, free
    extern __malloc_beg, __malloc_end
    segment text
    main:
    mov rax, __malloc_beg
    mov rbx, __malloc_end
    hlt

    mov edi, 0
    call calloc
    hlt

    mov edi, 645
    call calloc
    mov r15, rax
    hlt
    mov edi, 128
    call calloc
    mov r14, rax
    hlt
    mov rdi, r15
    call free
    hlt
    mov edi, 645
    call calloc
    hlt
    mov rdi, rax
    call free
    hlt
    mov edi, 656
    call calloc
    hlt
    mov rdi, rax
    call free
    hlt
    mov rdi, r14
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
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let first = e.cpu.get_rax();
    assert!(first >= base);
    assert_eq!(first, align_to(base, MALLOC_ALIGN) + 16);
    assert_eq!(first % MALLOC_ALIGN, 0);
    assert!(e.memory.get(first, 645).unwrap().iter().all(|&x| x == 0));
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 656)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let second = e.cpu.get_rax();
    assert_eq!(second, first + 656 + 16);
    assert_eq!(second % MALLOC_ALIGN, 0);
    assert!(e.memory.get(second, 128).unwrap().iter().all(|&x| x == 0));
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 656), (true, 128)]);
    e.memory.get_mut(second, 128).unwrap().copy_from_slice(&LONG_MESSAGE[445..445+128]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.memory.get(second, 128).unwrap(), &LONG_MESSAGE[445..445+128]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 656), (true, 128)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert!(e.memory.get(first, 645).unwrap().iter().all(|&x| x == 0));
    assert_eq!(e.memory.get(second, 128).unwrap(), &LONG_MESSAGE[445..445+128]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 656), (true, 128)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.memory.get(second, 128).unwrap(), &LONG_MESSAGE[445..445+128]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 656), (true, 128)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), first);
    assert!(e.memory.get(first, 656).unwrap().iter().all(|&x| x == 0));
    assert_eq!(e.memory.get(second, 128).unwrap(), &LONG_MESSAGE[445..445+128]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(true, 656), (true, 128)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.memory.get(second, 128).unwrap(), &LONG_MESSAGE[445..445+128]);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[(false, 656), (true, 128)]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(77));
}
#[test]
fn test_malloc_rand() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern realloc
    extern __malloc_beg, __malloc_end
    segment text
    main:
    mov rax, __malloc_beg
    mov rbx, __malloc_end

    top:
    hlt
    call realloc
    jmp top
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let base = e.cpu.get_rbp();
    assert_eq!(base, e.memory.len() as u64);
    let mut rng = rand::thread_rng();

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    let beg_ptr = e.cpu.get_rax();
    let end_ptr = e.cpu.get_rbx();
    assert_eq!(get_malloc_walk(&e.memory, beg_ptr, end_ptr), &[]);

    // allocate a bunch of memory locations and fill them with random content
    const ALLOC_COUNT: usize = 1024;
    const MAX_ALLOC_SIZE: u64 = 1024;
    let mut allocs: Vec<(u64, u64, Vec<u8>)> = Vec::with_capacity(ALLOC_COUNT);
    for _ in 0..ALLOC_COUNT {
        let raw_size = rng.next_u32() as u64 % MAX_ALLOC_SIZE + 1;
        let size = align_to(raw_size, MALLOC_ALIGN);

        e.cpu.set_rdi(0);
        e.cpu.set_rsi(raw_size); // raw_size is only passed to the machine - we use (aligned) size
        assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
        let pos = e.cpu.get_rax();
        println!("alloc {:#018x}:{}", pos, size); // in case the test fails, we need the random sequence it used
        
        // fill with random content
        let mut content = vec![0; size as usize];
        rng.fill_bytes(&mut content);
        e.memory.get_mut(pos, size).unwrap().copy_from_slice(&content);

        // check alignment and absolute positioning
        assert_eq!(pos % MALLOC_ALIGN, 0);
        if let Some(last) = allocs.last() {
            assert_eq!(pos, last.0 + 16 + last.1);
        }

        allocs.push((pos, size, content));
    }

    // make sure they all still have their content
    for (pos, size, content) in allocs.iter() {
        assert_eq!(e.memory.get(*pos, *size).unwrap(), content);
    }

    // randomize array so we perform the next step in undefined order
    allocs.shuffle(&mut rng);

    // resize everything and make sure they keep their content
    for i in 0..allocs.len() {
        let pos = allocs[i].0;
        let size = allocs[i].1;

        let raw_new_size = rng.next_u32() as u64 % MAX_ALLOC_SIZE + 1;
        let new_size = align_to(raw_new_size, MALLOC_ALIGN);

        e.cpu.set_rdi(pos);
        e.cpu.set_rsi(new_size);
        assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
        let new_pos = e.cpu.get_rax();
        println!("realloc {:#018x}:{} -> {:#018x}:{}", pos, size, new_pos, new_size);

        // make sure we still have the same content up to the smaller of the two sizes
        let min_size = new_size.min(size);
        assert_eq!(e.memory.get(new_pos, min_size).unwrap(), &allocs[i].2[..min_size as usize]);

        // get a new content array
        let mut new_content = vec![0; new_size as usize];
        rng.fill_bytes(&mut new_content);
        e.memory.get_mut(new_pos, new_size).unwrap().copy_from_slice(&new_content);

        allocs[i] = (new_pos, new_size, new_content);

        // make sure new array doesn't overlap with any others
        for other in allocs[..i].iter().chain(allocs[i+1..].iter()) {
            if new_pos + new_size <= other.0 - 16 { continue }
            if new_pos - 16 >= other.0 + other.1 { continue }
            panic!("intersecting allocations! {:#018x}:{} vs {:#018x}:{}", new_pos, new_size, other.0, other.1);
        }
    }

    // make sure they all still have their updated content
    for (pos, size, content) in allocs.iter() {
        assert_eq!(e.memory.get(*pos, *size).unwrap(), content);
    }
}

#[test]
fn test_atexit_1() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern atexit
    segment text
    f1:
        mov eax, 1
        hlt
        ret

    main:
        mov rdi, f1
        call atexit
        hlt

        mov eax, 420
        ret
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);

    // return from main()
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 1);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(420));
}
#[test]
fn test_atexit_2() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern atexit
    segment text
    f1:
        mov eax, 1
        hlt
        ret
    f2:
        mov eax, 2
        hlt
        ret

    main:
        mov rdi, f1
        call atexit
        hlt
        mov rdi, f2
        call atexit
        hlt

        mov eax, 420
        ret
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);

    // return from main()
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 2);
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 1);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(420));
}
#[test]
fn test_atexit_32() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern atexit
    segment text
    f1:
        mov eax, 1
        hlt
        ret
    f2:
        mov eax, 2
        hlt
        ret
    f3:
        mov eax, 3
        hlt
        ret
    f4:
        mov eax, 4
        hlt
        ret

    main:
        xor r15, r15
        .top:
            mov r14, r15
            and r14, 3
            mov rdi, [funcs + 8 * r14]
            debug_cpu
            call atexit
            hlt
            inc r15
            cmp r15, 32
            jb .top

        mov eax, 420
        ret
    
    segment rodata
    funcs: dq f1, f2, f3, f4
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    for i in 0..32 {
        assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
        if e.cpu.get_rax() != 0 { panic!("failed atexit {} with {}", i, e.cpu.get_rax()) }
    }

    // return from main()
    for _ in 0..8 {
        for i in (1..=4).rev() {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.cpu.get_rax(), i);
        }
    }

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(420));
}
#[test]
fn test_atexit_add_hook_during_exit() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern atexit
    segment text
    f:
        mov rdi, f
        call atexit
        hlt
        ret

    main:
        mov rdi, f
        call atexit
        hlt

        mov eax, 621
        ret
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);

    // return from main()
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 1);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(621));
}
#[test]
fn test_atexit_exit_during_exit() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern atexit, exit
    segment text
    f:
        mov rdi, 434
        call exit
        times 16 hlt ; this shouldn't be executed

    main:
        mov rdi, f
        call atexit
        hlt

        mov eax, 621
        ret
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), 0);

    // return from main()
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(-1));
}
#[test]
fn test_abort() {
    let exe = asm_unwrap_link_unwrap!(std r"
    global main
    extern abort
    segment text
    main:
        call abort
        times 16 hlt
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(-1));
}