use super::*;
use crate::exec::*;
use crate::exec::registers::Flags;

const ZSPACO: u64 = mask!(Flags: MASK_ZF | MASK_SF | MASK_PF | MASK_AF | MASK_CF | MASK_OF);
const ZSPCO: u64 = mask!(Flags: MASK_ZF | MASK_SF | MASK_PF | MASK_CF | MASK_OF);
const CO: u64 = mask!(Flags: MASK_CF | MASK_OF);
const ACCDI: u64 = mask!(Flags: MASK_AC | MASK_CF | MASK_DF | MASK_IF);

fn get_conditions(flags: Flags) -> ((bool, bool, bool, bool), (bool, bool, bool, bool)) {
    let b = flags.condition_b();
    let be = flags.condition_be();
    let a = flags.condition_a();
    let ae = flags.condition_ae();
    let unsigned = (b, be, a, ae);

    let l = flags.condition_l();
    let le = flags.condition_le();
    let g = flags.condition_g();
    let ge = flags.condition_ge();
    let signed = (l, le, g, ge);

    (unsigned, signed)
}

#[test]
fn test_mov_basic() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rax, -7784568640113865156
    mov rbx, 0x12de639fcd11a4cb
    mov rcx, 0x046579a453add4b8
    mov rdx, 0o1764420727724002664106
    mov rsi, 0xf1c89e98daa39a38
    mov rdi, 0xbdb00d43f2aaff23
    mov rbp, -7740818_22331708_3_744
    mov rsp, 0xa228b0bd6d86600e
    mov r8, 0x076899314a3e420b
    mov r9, 417771020883113582
    mov r10, 0x781b5ce0538f3fd0
    mov r11, 0x2569467b20f81cb8
    mov r12, 0xc0a9ed7647a335c4
    mov r13, 0o17052_7_0_262065_065_624_265___
    mov r14, 0x65902d29eac939fb
    mov r15, 0xec7aa569a6155ab1
    hlt
    mov eax, 0x7d22cbb4
    mov ebx, 0xbecb162e
    mov ecx, 0x___ae23158e
    mov edx, 0x0ddfe51b
    mov esi, 0o24_734_613_417
    mov edi, 0xa71a36d7
    mov ebp, 0xd130b0c0
    mov esp, 2209513684
    mov r8d, 0x___a53b___7___121___
    mov r9d, 0x74c9e6d0
    mov r10d, 0x58b7c4e7
    mov r11d, 0b11001010101111101111111010010001
    mov r12d, 0xaa92e8b4
    mov r13d, 0x86bbdbc1
    mov r14d, 0b_0111_1001_1111_0100_1110_0011_0100_1000
    mov r15d, 0xc023567e
    hlt
    mov ax, 0xcb04
    mov bx, 0x43f4
    mov cx, 0x6493
    mov dx, 0xacd9
    mov si, 0xf019
    mov di, 32_038
    mov bp, 0x60f1
    mov sp, 0x6476
    mov r8w, 0x3329
    mov r9w, 0x09f4
    mov r10w, 0x2cd7
    mov r11w, 0x6b08
    mov r12w, 0x3644
    mov r13w, 0x217f
    mov r14w, 0xb5a4
    mov r15w, 0x8df6
    hlt
    mov al, 0x1f
    mov bl, 0x5d
    mov cl, 0x82
    mov dl, 0xfb
    mov sil, 0x83
    mov dil, 0x78
    mov bpl, 0x45
    mov spl, 0x08
    mov r8b, 0xc6
    mov r9b, 0x5a
    mov r10b, 0xd2
    mov r11b, 0x3e
    mov r12b, 0x87
    mov r13b, 0x48
    mov r14b, 0x94
    mov r15b, 0x05
    hlt
    mov ah, 0x8c
    mov bh, 0xae
    mov ch, 0xe1
    mov dh, 0xaf
    hlt
    mov r8b, ah
    mov r9b, bh
    mov r10b, ch
    mov r11b, dh
    hlt
    mov eax, 0
    mov ebx, 0xfe630756
    syscall
    times 256 nop
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x93f7a810f45e0e3c);
    assert_eq!(e.cpu.get_rbx(), 0x12de639fcd11a4cb);
    assert_eq!(e.cpu.get_rcx(), 0x046579a453add4b8);
    assert_eq!(e.cpu.get_rdx(), 0xfd221d7ea00b6846);
    assert_eq!(e.cpu.get_rsi(), 0xf1c89e98daa39a38);
    assert_eq!(e.cpu.get_rdi(), 0xbdb00d43f2aaff23);
    assert_eq!(e.cpu.get_rbp(), 0x949316d6a85099a0);
    assert_eq!(e.cpu.get_rsp(), 0xa228b0bd6d86600e);
    assert_eq!(e.cpu.get_r8(),  0x076899314a3e420b);
    assert_eq!(e.cpu.get_r9(),  0x05cc3887b130b66e);
    assert_eq!(e.cpu.get_r10(), 0x781b5ce0538f3fd0);
    assert_eq!(e.cpu.get_r11(), 0x2569467b20f81cb8);
    assert_eq!(e.cpu.get_r12(), 0xc0a9ed7647a335c4);
    assert_eq!(e.cpu.get_r13(), 0xf1570b21a8d728b5);
    assert_eq!(e.cpu.get_r14(), 0x65902d29eac939fb);
    assert_eq!(e.cpu.get_r15(), 0xec7aa569a6155ab1);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x000000007d22cbb4);
    assert_eq!(e.cpu.get_rbx(), 0x00000000becb162e);
    assert_eq!(e.cpu.get_rcx(), 0x00000000ae23158e);
    assert_eq!(e.cpu.get_rdx(), 0x000000000ddfe51b);
    assert_eq!(e.cpu.get_rsi(), 0x00000000a773170f);
    assert_eq!(e.cpu.get_rdi(), 0x00000000a71a36d7);
    assert_eq!(e.cpu.get_rbp(), 0x00000000d130b0c0);
    assert_eq!(e.cpu.get_rsp(), 0x0000000083b280d4);
    assert_eq!(e.cpu.get_r8(),  0x00000000a53b7121);
    assert_eq!(e.cpu.get_r9(),  0x0000000074c9e6d0);
    assert_eq!(e.cpu.get_r10(), 0x0000000058b7c4e7);
    assert_eq!(e.cpu.get_r11(), 0x00000000cabefe91);
    assert_eq!(e.cpu.get_r12(), 0x00000000aa92e8b4);
    assert_eq!(e.cpu.get_r13(), 0x0000000086bbdbc1);
    assert_eq!(e.cpu.get_r14(), 0x0000000079f4e348);
    assert_eq!(e.cpu.get_r15(), 0x00000000c023567e);
    assert_eq!(e.flags.0, prev_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x000000007d22cb04);
    assert_eq!(e.cpu.get_rbx(), 0x00000000becb43f4);
    assert_eq!(e.cpu.get_rcx(), 0x00000000ae236493);
    assert_eq!(e.cpu.get_rdx(), 0x000000000ddfacd9);
    assert_eq!(e.cpu.get_rsi(), 0x00000000a773f019);
    assert_eq!(e.cpu.get_rdi(), 0x00000000a71a7d26);
    assert_eq!(e.cpu.get_rbp(), 0x00000000d13060f1);
    assert_eq!(e.cpu.get_rsp(), 0x0000000083b26476);
    assert_eq!(e.cpu.get_r8(),  0x00000000a53b3329);
    assert_eq!(e.cpu.get_r9(),  0x0000000074c909f4);
    assert_eq!(e.cpu.get_r10(), 0x0000000058b72cd7);
    assert_eq!(e.cpu.get_r11(), 0x00000000cabe6b08);
    assert_eq!(e.cpu.get_r12(), 0x00000000aa923644);
    assert_eq!(e.cpu.get_r13(), 0x0000000086bb217f);
    assert_eq!(e.cpu.get_r14(), 0x0000000079f4b5a4);
    assert_eq!(e.cpu.get_r15(), 0x00000000c0238df6);
    assert_eq!(e.flags.0, prev_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x000000007d22cb1f);
    assert_eq!(e.cpu.get_rbx(), 0x00000000becb435d);
    assert_eq!(e.cpu.get_rcx(), 0x00000000ae236482);
    assert_eq!(e.cpu.get_rdx(), 0x000000000ddfacfb);
    assert_eq!(e.cpu.get_rsi(), 0x00000000a773f083);
    assert_eq!(e.cpu.get_rdi(), 0x00000000a71a7d78);
    assert_eq!(e.cpu.get_rbp(), 0x00000000d1306045);
    assert_eq!(e.cpu.get_rsp(), 0x0000000083b26408);
    assert_eq!(e.cpu.get_r8(),  0x00000000a53b33c6);
    assert_eq!(e.cpu.get_r9(),  0x0000000074c9095a);
    assert_eq!(e.cpu.get_r10(), 0x0000000058b72cd2);
    assert_eq!(e.cpu.get_r11(), 0x00000000cabe6b3e);
    assert_eq!(e.cpu.get_r12(), 0x00000000aa923687);
    assert_eq!(e.cpu.get_r13(), 0x0000000086bb2148);
    assert_eq!(e.cpu.get_r14(), 0x0000000079f4b594);
    assert_eq!(e.cpu.get_r15(), 0x00000000c0238d05);
    assert_eq!(e.flags.0, prev_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x000000007d228c1f);
    assert_eq!(e.cpu.get_rbx(), 0x00000000becbae5d);
    assert_eq!(e.cpu.get_rcx(), 0x00000000ae23e182);
    assert_eq!(e.cpu.get_rdx(), 0x000000000ddfaffb);
    assert_eq!(e.flags.0, prev_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r8(),  0x00000000a53b338c);
    assert_eq!(e.cpu.get_r9(),  0x0000000074c909ae);
    assert_eq!(e.cpu.get_r10(), 0x0000000058b72ce1);
    assert_eq!(e.cpu.get_r11(), 0x00000000cabe6baf);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0xfe630756u32 as i32)));
    assert_eq!(e.get_state(), State::Terminated(0xfe630756u32 as i32));

    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_mov() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rax, 12
    mov ebx, -3
    mov di, 2
    mov r8d, [val]
    mov r9d, [dest1]
    mov [dest1], dword 23
    mov [dest2], ebx
    mov r10, rdi
    mov r14, dest1
    mov r15, dest2
    hlt

    mov eax, [float1]
    mov rbx, [float2]
    hlt

    mov edi, [dest1]
    mov esi, [dest2]
    mov eax, 0
    mov ebx, 54
    syscall
    times 50 nop

    segment rodata
    val: dd 22
    val2: dd 22
    val3: dd 22.2

    float1: dd 3.141_59
    float2: dq 3__._14_159__

    segment bss
    align 4
    dest1: resd 1
    dest2: resd 1
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(3), (3, StopReason::MaxCycles));
    assert_eq!(e.execute_cycles(u64::MAX), (8, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 12);
    assert_eq!(e.cpu.get_rbx(), 0xfffffffd);
    assert_eq!(e.cpu.get_rdi(), 2);
    assert_eq!(e.cpu.get_r8(), 22);
    assert_eq!(e.cpu.get_r9(), 0);
    assert_eq!(e.cpu.get_r10(), e.cpu.get_rdi());
    assert_eq!(e.memory.get_u32(e.cpu.get_r14()).unwrap(), 23);
    assert_eq!(e.memory.get_u32(e.cpu.get_r15()).unwrap(), e.cpu.get_ebx());
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 3.14159f32.to_bits() as u64);
    assert_eq!(e.cpu.get_rbx(), 3.14159f64.to_bits());
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::Terminated(54)));
    assert_eq!(e.get_state(), State::Terminated(54));
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}
#[test]
fn test_mov_cc() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0xfe12
    cmp ax, 12
    movg ah, al
    hlt
    cmp ax, 12
    movle ah, al
    hlt
    xor eax, eax
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    
    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xfe12);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x1212);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_add() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, -1
    add ax, 22
    hlt
    add [val], rax
    mov rbx, [val]
    hlt
    mov eax, -5
    add eax, 5
    hlt
    add eax, 1
    hlt
    add eax, 1
    hlt
    add eax, 1
    hlt
    add eax, -20
    hlt
    add eax, 1
    hlt
    mov eax, 0xffffffff
    add eax, 1
    hlt
    mov eax, 0x7fffffff
    add eax, 1
    hlt
    mov eax, 0xf
    add eax, 1
    hlt
    mov eax, 0
    mov ebx, 0
    syscall
    segment data
    val: dq 0x623
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x00000000ffff0015);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x00000000ffff0015);
    assert_eq!(e.cpu.get_rbx(), 0x00000000ffff0638);
    assert_eq!(e.flags.0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF | MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 1);
    assert_eq!(e.flags.0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 2);
    assert_eq!(e.flags.0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 3);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x00000000ffffffef);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x00000000fffffff0);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF | MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x0000000080000000);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 16);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_sub_cmp() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rax, 0xffffffff00000000 | 22
    sub eax, 19
    hlt
    cmp eax, 5
    hlt
    cmp eax, 3
    hlt
    sub eax, 2
    hlt
    mov ax, 0
    sub ax, 1
    hlt
    mov ax, 0x8000
    sub ax, 1
    hlt
    cmp ax, 0
    hlt
    sub ax, 0
    hlt
    mov eax, 0
    mov ebx, -1
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 3);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF));
    assert_eq!(get_conditions(e.flags), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 3);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_AF | MASK_CF));
    assert_eq!(get_conditions(e.flags), ((true, true, false, false), (true, true, false, false)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 3);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF));
    assert_eq!(get_conditions(e.flags), ((false, true, false, true), (false, true, false, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 1);
    assert_eq!(e.flags.0 & ZSPACO, mask!());
    assert_eq!(get_conditions(e.flags), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF | MASK_CF));
    assert_eq!(get_conditions(e.flags), ((true, true, false, false), (true, true, false, false)));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x7fff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF | MASK_AF | MASK_OF));
    assert_eq!(get_conditions(e.flags), ((false, false, true, true), (true, true, false, false)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x7fff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF));
    assert_eq!(get_conditions(e.flags), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x7fff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF));
    assert_eq!(get_conditions(e.flags), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(-1)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_and_or_xor_test() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x0ff0
    mov bx, 0xf00f
    and ax, bx
    hlt
    or bx, 0xff
    hlt
    xor bx, 0xff00
    hlt
    test bx, 0xabcd
    hlt
    mov eax, 0
    mov ebx, 0
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.cpu.get_bx(), 0xf00f);
    assert_eq!(e.flags.0 & ZSPCO, mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0xf0ff);
    assert_eq!(e.flags.0 & ZSPCO, mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0x0fff);
    assert_eq!(e.flags.0 & ZSPCO, mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0x0fff);
    assert_eq!(e.flags.0 & ZSPCO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_binary_high_regs() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x0102
    mov bx, 0x1508
    add ah, bl
    hlt
    sub bl, ah
    hlt
    sub bh, ah
    hlt
    mov eax, 0
    mov ebx, 0
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x0902);
    assert_eq!(e.cpu.get_bx(), 0x1508);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x0902);
    assert_eq!(e.cpu.get_bx(), 0x15ff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x0902);
    assert_eq!(e.cpu.get_bx(), 0x0cff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF | MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}
#[test]
fn test_binary_addr_imm_size_combos() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov [val], dword 756
    mov rax, [val]
    hlt
    mov word ptr [val], -255
    mov rax, [val]
    hlt
    mov eax, 0
    mov ebx, 0
    syscall

    segment bss
    val: resq 1
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 756);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 255u16.wrapping_neg() as u64);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_lea() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rax, 412
    mov rbx, 323
    mov r14, -30
    mov r15, -55
    mov ecx, 0
    hlt
    lea rcx, [rax + rbx ]
    lea rdx, [1*rbx + 1*rax]
    lea rsi, zword ptr [rax + 2*rbx]
    lea rdi, [rax + 4*rbx]
    lea r8, [rax + 8*rbx]
    lea r9, word ptr [rax + rbx + 100]
    lea r10, [rax + 2*rbx + 120]
    lea r11, qword ptr [2*rax + rbx - 130]
    lea r12, [rax + 4*rbx + 0]
    lea r13, [8*rax + 1*rbx - 143]
    hlt
    lea rcx, [2*rax - rax + rbx]
    lea rdx, [rax*3 + 20]
    lea rsi, zword ptr [5*rbx + 20]
    lea rdi, [rax*9 - 10]
    hlt
    lea rcx, [r14 + r15]
    lea edx, yword ptr [r14 + r15]
    lea si, [r14 + r15]
    lea rdi, [r14d + r15d + R15d]
    lea r8d, [r14d + r15d + r15d]
    lea r9w, xword ptr [r14d + r15d + r15d]
    lea r10, [r14w + 2*r15w*2]
    lea r11d, [r14w + 2*r15w*2]
    lea r12w, word ptr [r14w + 2*r15w*2]
    hlt
    lea rcx, [3   *(2 *r15 + r15)]
    lea edx, [3*    (2*r15 + r15)   ]
    lea si, yword ptr [   3*(2*r15 + r15)]
    lea rdi, [3*-(2*-r14d - --++-+-+r14d)]
    lea r8d, [3*-(2*-r14d - --++-+-+r14d)]
    lea r9w, qword ptr [3*-(2*-r14d - --++-+-+r14d)]
    lea r10, [3*-(2*-ax - --++-+-+aX) - 1*1*3*1*1*Ax*1*1*3*1*1 + r14w + 8*r15w]
    lea r11d, byte ptr [3*-(2 *- ax - --++ -+- +AX) - 1*1*3*1*1*ax*1*1*3*1*1 + r14w + 8*r15w]
    lea r12w, [3*-(2*-AX- --++-+-+aX) - 1*1*3*1*1*ax*1*1*3*1*1 + r14w + 8*r15w]
    hlt
    lea rcx, xword ptr [(rax + 212) * 2]
    lea rdx, [(rax - 222) * 2]
    lea rsi, [(22+rax)*4]
    lea rdi, dword ptr [(29 -rax) * -4]
    lea r8, [  8 * (     rax + 21)]
    lea r9, [8 * (rax - 20)]
    lea r10, [2 * (7 + rax)]
    lea r11, byte ptr [-  2 * (7 - rax)]
    hlt
    lea rcx, [rax]
    lea rdx, [rbx]
    lea rsi, [1*rax]
    lea rdi, [rbx*1]
    hlt
    lea rcx, [-423]
    lea rdx, [qword -423  ]
    lea rsi, [ dword - 423]
    lea rdi, [word    -423    ]
    hlt
    mov eax, 0
    mov ebx, 0
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (6, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 412);
    assert_eq!(e.cpu.get_rbx(), 323);
    assert_eq!(e.cpu.get_rcx(), 0);
    assert_eq!(e.cpu.get_r14(), 0xffffffffffffffe2);
    assert_eq!(e.cpu.get_r15(), 0xffffffffffffffc9);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (11, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 412 + 323);
    assert_eq!(e.cpu.get_rdx(), 412 + 323);
    assert_eq!(e.cpu.get_rsi(), 412 + 2 * 323);
    assert_eq!(e.cpu.get_rdi(), 412 + 4 * 323);
    assert_eq!(e.cpu.get_r8(), 412 + 8 * 323);
    assert_eq!(e.cpu.get_r9(), 412 + 323 + 100);
    assert_eq!(e.cpu.get_r10(), 412 + 2 * 323 + 120);
    assert_eq!(e.cpu.get_r11(), 2 * 412 + 323 - 130);
    assert_eq!(e.cpu.get_r12(), 412 + 4 * 323);
    assert_eq!(e.cpu.get_r13(), 8 * 412 + 323 - 143);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 412 + 323);
    assert_eq!(e.cpu.get_rdx(), 3 * 412 + 20);
    assert_eq!(e.cpu.get_rsi(), 5 * 323 + 20);
    assert_eq!(e.cpu.get_rdi(), 9 * 412 - 10);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (10, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xffffffffffffffab);
    assert_eq!(e.cpu.get_rdx(), 0x00000000ffffffab);
    assert_eq!(e.cpu.get_si(), 0xffab);
    assert_eq!(e.cpu.get_rdi(), 0x00000000ffffff74);
    assert_eq!(e.cpu.get_r8(), 0x00000000ffffff74);
    assert_eq!(e.cpu.get_r9w(), 0xff74);
    assert_eq!(e.cpu.get_r10(), 0x000000000000ff06);
    assert_eq!(e.cpu.get_r11(), 0x000000000000ff06);
    assert_eq!(e.cpu.get_r12w(), 0xff06);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (10, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xfffffffffffffe11);
    assert_eq!(e.cpu.get_rdx(), 0x00000000fffffe11);
    assert_eq!(e.cpu.get_si(), 0xfe11);
    assert_eq!(e.cpu.get_rdi(), 0x00000000fffffef2);
    assert_eq!(e.cpu.get_r8(), 0x00000000fffffef2);
    assert_eq!(e.cpu.get_r9w(), 0xfef2);
    assert_eq!(e.cpu.get_r10(), 0x000000000000fe2a);
    assert_eq!(e.cpu.get_r11(), 0x000000000000fe2a);
    assert_eq!(e.cpu.get_r12w(), 0xfe2a);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (9, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 1248);
    assert_eq!(e.cpu.get_rdx(), 380);
    assert_eq!(e.cpu.get_rsi(), 1736);
    assert_eq!(e.cpu.get_rdi(), 1532);
    assert_eq!(e.cpu.get_r8(), 3464);
    assert_eq!(e.cpu.get_r9(), 3136);
    assert_eq!(e.cpu.get_r10(), 838);
    assert_eq!(e.cpu.get_r11(), 810);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 412);
    assert_eq!(e.cpu.get_rdx(), 323);
    assert_eq!(e.cpu.get_rsi(), 412);
    assert_eq!(e.cpu.get_rdi(), 323);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xfffffffffffffe59);
    assert_eq!(e.cpu.get_rdx(), 0xfffffffffffffe59);
    assert_eq!(e.cpu.get_rsi(), 0x00000000fffffe59);
    assert_eq!(e.cpu.get_rdi(), 0x000000000000fe59);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_xchg() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rax, -1
    mov rbx, -2
    xchg rax, rbx
    hlt
    xchg eax, ebx
    hlt
    xchg bl, bh
    hlt
    xchg bh, al
    hlt
    xchg bx, [val]
    mov rcx, [val]
    hlt
    xchg [val], bh
    mov rcx, [val]
    hlt
    xchg rcx, rcx
    hlt
    mov eax, 0
    mov ebx, 0
    syscall

    segment data
    val: dq 0x3543
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xfffffffffffffffe);
    assert_eq!(e.cpu.get_rbx(), 0xffffffffffffffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffffffff);
    assert_eq!(e.cpu.get_rbx(), 0xfffffffe);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffffffff);
    assert_eq!(e.cpu.get_rbx(), 0xfffffeff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xfffffffe);
    assert_eq!(e.cpu.get_rbx(), 0xffffffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xfffffffe);
    assert_eq!(e.cpu.get_rbx(), 0xffff3543);
    assert_eq!(e.cpu.get_rcx(), 0xffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xfffffffe);
    assert_eq!(e.cpu.get_rbx(), 0xffffff43);
    assert_eq!(e.cpu.get_rcx(), 0xff35);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xff35);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_jmp() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rax, again
    mov ebx, 123
    jmp next
    times 16 nop
    hlt

    again:
    hlt
    mov ebx, 2232
    jmp qword ptr [finally]
    times 16 nop
    hlt

    next:
    hlt
    mov ebx, 1222
    jmp rax
    times 16 nop
    hlt

    stop:
    hlt
    mov eax, 0
    mov ebx, 0
    syscall
    times 16 nop
    hlt

    segment rodata
    finally: dq stop
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ebx(), 123);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ebx(), 1222);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ebx(), 2232);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_jcc() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    xor eax, eax
    mov ebx, 12
    cmp eax, 0
    jne stop
    mov ebx, 123
    je other
    times 16 nop
    hlt

    other:
    hlt
    cmp eax, 2
    jg .skip
    mov ebx, 66
    jl stop
    .skip: times 20 nop
    hlt

    stop:
    hlt
    mov eax, 0
    mov ebx, 0
    syscall
    times 16 nop
    hlt

    segment rodata
    finally: dq stop
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (7, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_eax(), 0);
    assert_eq!(e.cpu.get_ebx(), 123);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_eax(), 0);
    assert_eq!(e.cpu.get_ebx(), 66);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_call_ret_loop() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov edi, 6
    call sum
    hlt
    mov edi, 17
    call sum
    hlt
    mov edi, 0
    call sum
    hlt
    mov edi, 200
    call sum
    hlt

    mov eax, 0
    mov ebx, 0
    syscall

    sum:
    xor rax, rax
    mov rcx, rdi
    jrcxz .done
    .top:
        add rax, rcx
        loop .top
    .done:
    ret
    times 16 nop
    hlt
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (19, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 21);

    assert_eq!(e.execute_cycles(u64::MAX), (41, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 153);

    assert_eq!(e.execute_cycles(u64::MAX), (7, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (407, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 20100);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_push_pop() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x1234
    push ax
    push dword 0x6546
    hlt
    pop ax
    pop bx
    pop cx
    hlt
    push qword ptr [thing]
    pop qword ptr [other]
    mov rax, [other]
    hlt
    xor eax, eax
    xor ebx, ebx
    syscall

    segment data
    thing: dq 0x0102030405060708
    other: dq -1
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let stack_start = e.cpu.get_rsp();

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsp(), stack_start - 6);
    assert_eq!(e.memory.get_u16(stack_start - 2).unwrap(), 0x1234);
    assert_eq!(e.memory.get_u32(stack_start - 6).unwrap(), 0x6546);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsp(), stack_start);
    assert_eq!(e.memory.get_u16(stack_start - 2).unwrap(), 0x1234); // they should still be there
    assert_eq!(e.memory.get_u32(stack_start - 6).unwrap(), 0x6546);
    assert_eq!(e.cpu.get_ax(), 0x6546);
    assert_eq!(e.cpu.get_bx(), 0x0000);
    assert_eq!(e.cpu.get_cx(), 0x1234);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsp(), stack_start);
    assert_eq!(e.memory.get_u64(stack_start - 8).unwrap(), 0x0102030405060708); // it should still be there
    assert_eq!(e.cpu.get_rax(), 0x0102030405060708);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_stack_underflow() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    pop ax
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::Error(ExecError::StackUnderflow)));
    assert_eq!(e.get_state(), State::Error(ExecError::StackUnderflow));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}
#[test]
fn test_stack_overflow() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov r9, thing
    hlt

    top:
    push qword 0x0102030405060708
    jmp top
    
    segment bss
    thing: resb 1
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    let thing = e.cpu.get_r9();
    assert_eq!(e.memory.get_u8(thing).unwrap(), 0);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Error(ExecError::StackOverflow));
    assert_eq!(e.get_state(), State::Error(ExecError::StackOverflow));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
    assert_eq!(e.memory.get_u8(thing).unwrap(), 0); // we shouldn't have overwritten anything outside of stack
}

#[test]
fn test_inc() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, -2
    inc eax
    hlt
    inc eax
    hlt
    inc eax
    hlt
    inc word ptr [val]
    mov bx, [val]
    hlt
    inc word ptr [val]
    mov bx, [val]
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall

    segment data
    val: dw 0x7fff
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert!(!e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffffffff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF | MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 1);
    assert_eq!(e.flags.0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0x8000);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0x8001);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_dec() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, 2
    dec eax
    hlt
    dec eax
    hlt
    dec eax
    hlt
    dec word ptr [val]
    mov bx, [val]
    hlt
    dec word ptr [val]
    mov bx, [val]
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall

    segment data
    val: dw 0x8000
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert!(!e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 1);
    assert_eq!(e.flags.0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffffffff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0x7fff);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_PF | MASK_AF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_bx(), 0x7ffe);
    assert_eq!(e.flags.0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_neg() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, 2
    neg eax
    hlt
    neg ax
    hlt
    mov eax, 0x80000000
    neg eax
    hlt
    xor eax, eax
    neg eax
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xfffffffe);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffff0002);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x80000000);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_not() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, 0xdeadbeef
    not eax
    hlt
    not rax
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x21524110);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffffffffdeadbeef);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_mul_1() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rdx, 0xdeadbeefdeadbeef
    mov eax, 0xabcd0007
    mul word 3
    hlt
    mov ch, -30
    mul ch
    hlt
    mov rax, 0xdeadbeefffffffff
    mul dword -1
    hlt
    mov rax, -6
    mul qword 632
    hlt
    mov al, 2
    mul byte -1
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 0xdeadbeefdead0000);
    assert_eq!(e.cpu.get_rax(), 0xabcd0015);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xabcd128a);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 0xfffffffe);
    assert_eq!(e.cpu.get_rax(), 1);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 0x0000000000000277);
    assert_eq!(e.cpu.get_rax(), 0xfffffffffffff130);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x01fe);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_mul_2() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rdi, 0xdeadbeefdeadbeef
    mov ebx, 0xabcd0007
    mul bx, 3
    hlt
    mov ch, -30
    mul bl, ch
    hlt
    mov rsi, 0xdeadbeefffffffff
    mul esi, -1
    hlt
    mov r9, -6
    mul r9, 632
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xabcd0015);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xabcd008a);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), 1);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r9(), 0xfffffffffffff130);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_mul_3() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rdi, 0xdeadbeefdeadbeef
    mov ebx, 0xabcd0007
    mul di, bx, 3
    hlt
    mov ch, -30
    mul bh, dil, ch
    hlt
    mov rsi, 0xdeadbeefffffffff
    mul esi, esi, -1
    hlt
    mov r9, -6
    mul r10, r9, 632
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdi(), 0xdeadbeefdead0015);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xabcd8a07);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), 1);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r10(), 0xfffffffffffff130);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_mulx() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov r12, 0xdeadbeefdeadbeef
    mov edx, 0xabcd0007
    mulx r12w, r13w, 3
    hlt
    mov rdx, r13
    mov ch, -30
    mulx r14b, r15b, ch
    hlt
    mov rdx, 0xdeadbeefffffffff
    mulx edi, esi, -1
    hlt
    mov rdx, -6
    mulx rcx, rbx, 632
    hlt
    mov rdx, -6
    mulx rcx, rcx, 632
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r12(), 0xdeadbeefdead0000);
    assert_eq!(e.cpu.get_r13w(), 0x0015);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r14b(), 0x12);
    assert_eq!(e.cpu.get_r15b(), 0x8a);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_edi(), 0xfffffffe);
    assert_eq!(e.cpu.get_esi(), 1);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0x0000000000000277);
    assert_eq!(e.cpu.get_rbx(), 0xfffffffffffff130);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0x0000000000000277);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_imul_1() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rdx, 0xdeadbeefdeadbeef
    mov eax, 0xabcd0007
    imul word 3
    hlt
    mov ch, -30
    imul ch
    hlt
    mov rax, 0xdeadbeefffffffff
    imul dword -1
    hlt
    mov rax, -6
    imul qword 632
    hlt
    mov al, 2
    imul byte -1
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 0xdeadbeefdead0000);
    assert_eq!(e.cpu.get_rax(), 0xabcd0015);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xabcdfd8a);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 0);
    assert_eq!(e.cpu.get_rax(), 1);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 0xffffffffffffffff);
    assert_eq!(e.cpu.get_rax(), 0xfffffffffffff130);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xfffe);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_imul_2() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rdi, 0xdeadbeefdeadbeef
    mov ebx, 0xabcd0007
    imul bx, 3
    hlt
    mov ch, -30
    imul bl, ch
    hlt
    mov rsi, 0xdeadbeefffffffff
    imul esi, -1
    hlt
    mov r9, -6
    imul r9, 632
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xabcd0015);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xabcd008a);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), 1);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r9(), 0xfffffffffffff130);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_imul_3() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rdi, 0xdeadbeefdeadbeef
    mov ebx, 0xabcd0007
    imul di, bx, 3
    hlt
    mov ch, -30
    imul bh, dil, ch
    hlt
    mov rsi, 0xdeadbeefffffffff
    imul esi, esi, -1
    hlt
    mov r9, -6
    imul r10, r9, 632
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdi(), 0xdeadbeefdead0015);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xabcd8a07);
    assert_eq!(e.flags.0 & CO, CO);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), 1);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r10(), 0xfffffffffffff130);
    assert_eq!(e.flags.0 & CO, 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_imulx() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov r12, 0xdeadbeefdeadbeef
    mov edx, 0xabcd0007
    imulx r12w, r13w, 3
    hlt
    mov rdx, r13
    mov ch, -30
    imulx r14b, r15b, ch
    hlt
    mov rdx, 0xdeadbeefffffffff
    imulx edi, esi, -1
    hlt
    mov rdx, -6
    imulx rcx, rbx, 632
    hlt
    mov rdx, -6
    imulx rcx, rcx, 632
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r12(), 0xdeadbeefdead0000);
    assert_eq!(e.cpu.get_r13w(), 0x0015);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_r14b(), 0xfd);
    assert_eq!(e.cpu.get_r15b(), 0x8a);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_edi(), 0);
    assert_eq!(e.cpu.get_esi(), 1);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xffffffffffffffff);
    assert_eq!(e.cpu.get_rbx(), 0xfffffffffffff130);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xffffffffffffffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_div() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 20151
    div byte 87
    hlt
    mov dx, 0xd79e
    mov ax, 0x21a2
    mov bx, 60000
    div bx
    hlt
    mov edx, 0x3
    mov eax, 0xd5eb1dc0
    div dword ptr [leet]
    hlt
    mov rdx, 0xc18d48d68cf6b4a7
    mov rax, 0xa4cde210190cd45c
    div qword 17928594385485747293
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall

    segment rodata
    leet: dq 1337
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 54);
    assert_eq!(e.cpu.get_al(), 231);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_dx(), 4738);
    assert_eq!(e.cpu.get_ax(), 60291);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 1276);
    assert_eq!(e.cpu.get_rax(), 12321508);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 117491172663809773);
    assert_eq!(e.cpu.get_rax(), 14349959000900009019);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_div_errors() {
    let tests = &[
        ("segment text\ndiv byte 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv word 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv dword 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv qword 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\ndiv al", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\ndiv ah", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\ndiv ax", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\ndiv eax", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\ndiv rax", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv byte ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv word ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv dword ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\ndiv qword ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nmov ax, 20151\ndiv byte 78", (1, StopReason::Error(ExecError::DivisionOverflow))),
    ];
    let mut e = Emulator::new();
    for &(prog, expected) in tests {
        let exe = asm_unwrap_link_unwrap!(prog);
        e.init(&exe, &Default::default());
        assert_eq!(e.get_state(), State::Running);
        assert_eq!(e.execute_cycles(u64::MAX), expected);
    }
}
#[test]
fn test_idiv() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 12151
    mov ch, 101
    idiv ch
    hlt
    mov dx, 0xd79e
    mov ax, 0x21a2
    mov bx, 31563
    idiv bx
    hlt
    mov edx, 0x3
    mov eax, 0xd5eb1dc0
    idiv dword ptr [leet]
    hlt
    mov rdx, 0xf18d48d68cf6b4a7
    mov rax, 0xa4cde210190cd45c
    idiv qword 9928594385485747293
    hlt
    xor rax, rax
    xor rbx, rbx
    syscall

    segment rodata
    leet: dq -1337
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 31);
    assert_eq!(e.cpu.get_al(), 120);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_dx(), 2763u16.wrapping_neg());
    assert_eq!(e.cpu.get_ax(), 21465u16.wrapping_neg());

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 1276);
    assert_eq!(e.cpu.get_rax(), 12321508u32.wrapping_neg() as u64);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rdx(), 5539981218873602520u64.wrapping_neg());
    assert_eq!(e.cpu.get_rax(), 2254577513978919876);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_idiv_errors() {
    let tests = &[
        ("segment text\nidiv byte 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv word 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv dword 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv qword 0", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\nidiv al", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\nidiv ah", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\nidiv ax", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\nidiv eax", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nxor rax, rax\nidiv rax", (1, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv byte ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv word ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv dword ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nidiv qword ptr [val]\nsegment bss\nval: resq 1", (0, StopReason::Error(ExecError::DivideByZero))),
        ("segment text\nmov ax, 20151\nidiv byte 87", (1, StopReason::Error(ExecError::DivisionOverflow))),
    ];
    let mut e = Emulator::new();
    for &(prog, expected) in tests {
        let exe = asm_unwrap_link_unwrap!(prog);
        e.init(&exe, &Default::default());
        assert_eq!(e.get_state(), State::Running);
        assert_eq!(e.execute_cycles(u64::MAX), expected);
    }
}

#[test]
fn test_bit_regops() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    stac
    hlt
    stc
    hlt
    std
    hlt
    sti
    hlt
    
    cld
    hlt
    clac
    hlt
    clc
    hlt
    cli
    hlt

    cmi
    hlt
    cmac
    hlt
    cmi
    hlt
    cmc
    hlt
    cmd
    hlt
    cmc
    hlt
    cmac
    hlt
    cmd
    hlt

    xor rax, rax
    xor rbx, rbx
    syscall

    segment rodata
    leet: dq -1337
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_eq!(e.flags.0 & ACCDI, mask!());

    let expected = &[
        mask!(Flags: MASK_AC),
        mask!(Flags: MASK_AC | MASK_CF),
        mask!(Flags: MASK_AC | MASK_CF | MASK_DF),
        mask!(Flags: MASK_AC | MASK_CF | MASK_DF | MASK_IF),

        mask!(Flags: MASK_AC | MASK_CF | MASK_IF),
        mask!(Flags: MASK_CF | MASK_IF),
        mask!(Flags: MASK_IF),
        mask!(),

        mask!(Flags: MASK_IF),
        mask!(Flags: MASK_IF | MASK_AC),
        mask!(Flags: MASK_AC),
        mask!(Flags: MASK_AC | MASK_CF),
        mask!(Flags: MASK_AC | MASK_CF | MASK_DF),
        mask!(Flags: MASK_AC | MASK_DF),
        mask!(Flags: MASK_DF),
        mask!(),
    ];
    for &expect in expected {
        assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
        assert_eq!(e.flags.0 & ACCDI, expect);
    }

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_shl() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x20
    shl ax, 1
    hlt
    mov ax, 0x4000
    shl ax, [one]
    hlt
    shl ax, 1
    hlt
    mov eax, 5
    shl eax, 16
    hlt
    shl eax, 14
    hlt
    mov dh, 1
    shl eax, dh
    hlt
    shl eax, dh
    hlt
    shl eax, 1
    hlt
    mov rax, 0xc000000000000000
    shl rax, 1
    hlt
    shl rax, 1
    hlt
    mov ax, 0x3585
    shl ax, 20
    hlt
    mov ax, 0xffff
    shl ax, byte ptr [sixteen]
    hlt
    mov ax, 0xfffe
    shl ax, [sixteen]
    hlt
    mov eax, 0xdeadbeef
    shl eax, 0
    hlt
    mov ah, 0xff
    shl ah, 31
    hlt
    mov rbx, -1
    shl bx, 31
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment rodata
    sixteen: db 16
    one: db 1
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x40);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x8000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x00050000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x40000000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x80000000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x8000000000000000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    let prev_flags = e.flags.0;
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeef);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0xffffffffffff0000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_shr() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0xc000
    shr ax, 1
    hlt
    shr ax, 1
    hlt
    shr ax, 1
    hlt
    mov ax, 0x8000
    shr ax, 1
    hlt
    mov eax, 0xab10
    shr eax, 4
    hlt
    shr eax, 1
    hlt
    mov dil, 6
    shr eax, dil
    hlt
    shr eax, 5
    hlt
    mov eax, 0xdeadbeef
    shr eax, 40
    hlt
    mov eax, 0xdeadbeef
    shr eax, 32
    hlt
    mov ax, 0xbeef
    shr ax, 30
    hlt
    mov ax, 0xbeef
    shr ax, 16
    hlt
    mov ax, 0x5eef
    shr ax, 16
    hlt
    mov eax, 0xdeadbeef
    shr eax, 0
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x6000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x3000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x1800);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x4000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xab1);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x558);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x15);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbe);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF | MASK_CF));
    let prev_flags_1 = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeef);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    let prev_flags_2 = e.flags.0;
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeef);
    assert_eq!(e.flags.0, prev_flags_2);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_sar() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, -1
    sar ax, 1
    hlt
    mov ax, -2
    sar ax, byte ptr [one]
    hlt
    mov ax, 0x7800
    sar ax, 11
    hlt
    mov ax, 0x7800
    sar ax, 12
    hlt
    mov ax, 0x8000
    sar ax, 15
    hlt
    mov ax, 0x8000
    sar ax, 16
    hlt
    mov eax, 0x40384837
    sar eax, 40
    hlt
    mov ax, 0x4837
    mov bh, 30
    sar eax, bh
    hlt
    mov ax, 0x4837
    mov bh, 16
    sar eax, bh
    hlt
    mov ax, 0xc837
    sar eax, bh
    hlt
    mov eax, 0x40384837
    sar eax, 32
    hlt
    mov rax, 0xdeadbeefdeadbeef
    sar rax, 0
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment rodata
    one: db 1
    thirtytwo: db 32
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xf);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x7);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x403848);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_ZF | MASK_PF | MASK_CF));
    let prev_flags_1 = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x40384837);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeefdeadbeef);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_shlx() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x20
    shlx bx, ax, 1
    hlt
    mov ax, 0x4000
    shlx di, ax, [one]
    hlt
    shlx ax, di, 1
    hlt
    mov eax, 5
    shlx eax, eax, 16
    hlt
    shlx eax, eax, 14
    hlt
    mov dl, 1
    shlx ebx, eax, edx
    hlt
    shlx eax, ebx, edx
    hlt
    shlx eax, eax, 1
    hlt
    mov rax, 0xc000000000000000
    shlx r8, rax, 1
    hlt
    shlx rax, r8, 1
    hlt
    mov ax, 0x3585
    shlx ax, ax, 20
    hlt
    mov ax, 0xffff
    shlx si, ax, word ptr [sixteen]
    hlt
    mov ax, 0xfffe
    shlx ax, ax, [sixteen]
    hlt
    mov eax, 0xdeadbeef
    shlx eax, eax, 0
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment rodata
    sixteen: db 16
    one: db 1
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x20);
    assert_eq!(e.cpu.get_bx(), 0x40);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x4000);
    assert_eq!(e.cpu.get_di(), 0x8000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.cpu.get_di(), 0x8000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x00050000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x40000000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0x80000000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xc000000000000000);
    assert_eq!(e.cpu.get_r8(), 0x8000000000000000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.cpu.get_si(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeef);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_shrx() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0xc000
    shrx ax, ax, 1
    hlt
    shrx ax, ax, 1
    hlt
    shrx ax, ax, 1
    hlt
    mov ax, 0x8000
    shrx ax, ax, 1
    hlt
    mov eax, 0xab10
    shrx eax, eax, 4
    hlt
    shrx eax, eax, 1
    hlt
    mov dil, 6
    shrx eax, eax, edi
    hlt
    shrx eax, eax, 5
    hlt
    mov eax, 0xdeadbeef
    shrx eax, eax, 40
    hlt
    mov eax, 0xdeadbeef
    shrx eax, eax, 32
    hlt
    mov ax, 0xbeef
    shrx ax, ax, 30
    hlt
    mov ax, 0xbeef
    shrx ax, ax, 16
    hlt
    mov ax, 0x5eef
    shrx ax, ax, 16
    hlt
    mov eax, 0xdeadbeef
    shrx eax, eax, 0
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;
    
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x6000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x3000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x1800);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x4000);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xab1);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x558);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x15);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbe);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeef);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeef);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_sarx() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, -1
    sarx ax, ax, 1
    hlt
    mov ax, -2
    sarx ax, ax, word ptr [one]
    hlt
    mov ax, 0x7800
    sarx ax, ax, 11
    hlt
    mov ax, 0x7800
    sarx ax, ax, 12
    hlt
    mov ax, 0x8000
    sarx ax, ax, 15
    hlt
    mov ax, 0x8000
    sarx ax, ax, 16
    hlt
    mov eax, 0x40384837
    sarx eax, eax, 40
    hlt
    mov ax, 0x4837
    mov bl, 30
    sarx eax, eax, ebx
    hlt
    mov ax, 0x4837
    mov bh, 16
    sarx eax, eax, ebx
    hlt
    mov ax, 0xc837
    sarx eax, eax, ebx
    hlt
    mov eax, 0x40384837
    sarx eax, eax, 32
    hlt
    mov rax, 0xdeadbeefdeadbeef
    sarx rax, rax, 0
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment rodata
    one: db 1
    thirtytwo: db 32
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let prev_flags = e.flags.0;
    
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xf);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x7);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffff);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x403848);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x40384837);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xdeadbeefdeadbeef);
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_rol() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x0140
    rol ax, 8
    hlt
    mov ax, 0
    rol ax, 16
    hlt
    mov al, 0xc0
    rol al, 1
    hlt
    mov al, 0xa0
    rol al, 1
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x4001);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_CF));
    let prev_flags_1 = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_al(), 0x81);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_al(), 0x41);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_ror() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov ax, 0x0140
    ror ax, 8
    hlt
    mov ax, 0
    ror ax, 16
    hlt
    mov ah, 0x81
    ror ah, 1
    hlt
    mov ah, 1
    ror ah, 1
    hlt
    mov rax, 0x808000000000dead
    clc
    ror rax, 1
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x4001);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!());
    let prev_flags_1 = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0xc0);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0x80);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xc040000000006f56);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_rcl() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, 0x12345678
    stc
    rcl eax, 7
    hlt
    mov eax, 0x12345678
    clc
    rcl eax, 7
    hlt
    mov ax, 0xdead
    clc
    rcl ax, 16
    hlt
    mov ax, 0xdead
    stc
    rcl ax, 16
    hlt
    mov ax, 0xffee
    rcl ax, 17
    hlt
    mov ah, 0xfe
    rcl ah, 9
    hlt
    mov eax, 0xffee
    rcl eax, 0
    hlt
    mov rax, 0xffee1
    rcl rax, 0
    hlt
    mov ah, 0xc0
    clc
    rcl ah, 1
    hlt
    mov ah, 0xc0
    stc
    rcl ah, 1
    hlt
    mov rbx, 0xb000000000000000
    clc
    rcl rbx, 1
    hlt
    mov rbx, 0xb000000000000000
    stc
    rcl rbx, 1
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x1a2b3c44);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x1a2b3c04);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0x6f56);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xef56);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));
    let prev_flags_1 = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ax(), 0xffee);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0xfe);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffee);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xffee1);
    assert_eq!(e.flags.0, prev_flags_1);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0x80);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0x81);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0x6000000000000000);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rbx(), 0x6000000000000001);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}
#[test]
fn test_rcr() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, 0x12345678
    stc
    rcr eax, 7
    hlt
    mov eax, 0x12345678
    clc
    rcr eax, 7
    hlt
    mov eax, 0x12345678
    stc
    rcr eax, 8
    hlt
    mov eax, 0x12345678
    clc
    rcr eax, 8
    hlt
    mov ah, 0x6e
    clc
    rcr ah, 8
    hlt
    mov ah, 0x6e
    stc
    rcr ah, 8
    hlt
    mov rax, 0x8143646638765475
    stc
    rcr rax, 1
    hlt
    mov rax, 0x8143646638765475
    clc
    rcr rax, 1
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xe22468ac);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xe02468ac);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xf1123456);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xf0123456);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0xdc);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 0xdd);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF), mask!(Flags: MASK_SF | MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0xc0a1b2331c3b2a3a);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_SF | MASK_PF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0x40a1b2331c3b2a3a);
    assert_eq!(e.flags.0 & mask!(Flags: MASK_SF | MASK_ZF | MASK_PF | MASK_CF | MASK_OF), mask!(Flags: MASK_PF | MASK_CF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_setcc() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    clc
    setc eax
    hlt
    stc
    setc eax
    hlt
    mov eax, 358485
    cmp eax, 0
    sets qword ptr [val]
    mov rbx, [val]
    hlt
    mov ah, -5
    cmp ah, 0
    setl byte ptr [val]
    mov bh, [val]
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment data
    val: dq 3572785835
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 1);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 358485);
    assert_eq!(e.cpu.get_rbx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_ah(), 5u8.wrapping_neg());
    assert_eq!(e.cpu.get_bh(), 1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}

#[test]
fn test_bt() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    call check1
    call check1
    call check1

    mov edx, 0xdeadbeef
    call check2

    mov eax, sys_exit
    xor ebx, ebx
    syscall

    check1:
    xor ecx, ecx
    .top:
        bt [arr], ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    check2:
    xor ecx, ecx
    .top:
        bt edx, ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    segment rodata
    align 4
    arr: db 0x00, 0x69, 0x20, 0x0f, 0x00, 0xab, 0x56, 0x12, 0xff, 0x3c, 0x12, 0xd7
    align 4
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    
    for _ in 0..3 {
        for &(mut expect32) in &[0x0f206900u32, 0x1256ab00, 0xd7123cff] {
            for _ in 0..32 {
                assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
                assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
                expect32 >>= 1;
            }
        }
    }

    for &(mut expect32) in &[0xdeadbeefu32, 0xdeadbeef, 0xdeadbeef] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(0));
}
#[test]
fn test_btc() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov rcx, 0xdeadbeef01020304
    btc rcx, 53
    hlt
    btc rcx, 64
    hlt
    btc rcx, 0
    hlt

    call check1
    call check1
    call check1

    mov edx, 0xdeadbeef
    call check2

    mov eax, sys_exit
    xor ebx, ebx
    syscall

    check1:
    xor ecx, ecx
    .top:
        btc [arr], ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    check2:
    xor ecx, ecx
    .top:
        btc edx, ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    segment data
    align 4
    arr: db 0x00, 0x69, 0x20, 0x0f, 0x00, 0xab, 0x56, 0x12, 0xff, 0x3c, 0x12, 0xd7
    align 4
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xde8dbeef01020304);
    assert!(e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xde8dbeef01020305);
    assert!(!e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rcx(), 0xde8dbeef01020304);
    assert!(e.flags.get_cf());

    for &(mut expect32) in &[0x0f206900u32, 0x1256ab00, 0xd7123cff] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }
    for &(mut expect32) in &[0xf0df96ffu32, 0xeda954ff, 0x28edc300] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }
    for &(mut expect32) in &[0x0f206900u32, 0x1256ab00, 0xd7123cff] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }

    for &(mut expect32) in &[0xdeadbeefu32, 0x21524110, 0xdeadbeef] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(0));
}
#[test]
fn test_bts() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov cx, 0x5476
    bts cx, 20
    hlt
    bts cx, 9
    hlt
    bts cx, 9
    hlt

    call check1
    call check1
    call check1

    mov edx, 0xdeadbeef
    call check2

    mov eax, sys_exit
    xor ebx, ebx
    syscall

    check1:
    xor ecx, ecx
    .top:
        bts [arr], ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    check2:
    xor ecx, ecx
    .top:
        bts edx, ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    segment data
    align 4
    arr: db 0x00, 0x69, 0x20, 0x0f, 0x00, 0xab, 0x56, 0x12, 0xff, 0x3c, 0x12, 0xd7
    align 4
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_cx(), 0x5476);
    assert!(e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_cx(), 0x5676);
    assert!(!e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_cx(), 0x5676);
    assert!(e.flags.get_cf());

    for &(mut expect32) in &[0x0f206900u32, 0x1256ab00, 0xd7123cff] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }
    for _ in 0..2 {
        for &(mut expect32) in &[0xffffffffu32, 0xffffffff, 0xffffffff] {
            for _ in 0..32 {
                assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
                assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
                expect32 >>= 1;
            }
        }
    }

    for &(mut expect32) in &[0xdeadbeefu32, 0xffffffff, 0xffffffff] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(0));
}
#[test]
fn test_btr() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov dl, 0x67
    btr dl, 10
    hlt
    btr dl, 0
    hlt
    btr dl, 0
    hlt

    call check1
    call check1
    call check1

    mov edx, 0xdeadbeef
    call check2

    mov eax, sys_exit
    xor ebx, ebx
    syscall

    check1:
    xor ecx, ecx
    .top:
        btr [arr], ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    check2:
    xor ecx, ecx
    .top:
        btr edx, ecx
        hlt
    inc ecx
    cmp ecx, 96
    jb .top
    ret

    segment data
    align 4
    arr: db 0x00, 0x69, 0x20, 0x0f, 0x00, 0xab, 0x56, 0x12, 0xff, 0x3c, 0x12, 0xd7
    align 4
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_dl(), 0x63);
    assert!(e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_dl(), 0x62);
    assert!(e.flags.get_cf());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_dl(), 0x62);
    assert!(!e.flags.get_cf());

    for &(mut expect32) in &[0x0f206900u32, 0x1256ab00, 0xd7123cff] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }
    for _ in 0..2 {
        for &(mut expect32) in &[0u32, 0, 0] {
            for _ in 0..32 {
                assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
                assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
                expect32 >>= 1;
            }
        }
    }

    for &(mut expect32) in &[0xdeadbeefu32, 0, 0] {
        for _ in 0..32 {
            assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
            assert_eq!(e.flags.get_cf(), expect32 & 1 != 0);
            expect32 >>= 1;
        }
    }

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(0));
}

#[test]
fn test_movs() {
    let exe = asm_unwrap_link_unwrap!(r#"
    segment text
    mov rsi, arr1
    mov rdi, arr2
    hlt
    cld
    movsb
    hlt
    lea rsi, [arr1 + 17]
    lea rdi, [arr2 + 17]
    cld
    movsd
    hlt
    lea rsi, [arr1 + 30]
    lea rdi, [arr2 + 0]
    std
    movsq
    hlt
    lea rsi, [arr2 + 0]
    lea rdi, [arr2 + 1]
    mov ecx, 6
    cld
    rep movsb
    hlt
    lea rsi, [arr1 + 0]
    lea rdi, [arr1 + 1]
    mov ecx, 4
    cld
    rep movsw
    hlt
    lea rsi, [arr1 + 34]
    lea rdi, [arr1 + 31]
    mov ecx, 3
    std
    rep movsq
    hlt
    lea rsi, [arr2 + 40]
    lea rdi, [arr2 + 33]
    mov ecx, 20
    std
    rep movsb
    hlt
    mov ecx, 0
    rep movsb
    hlt
    mov ecx, 0
    rep movsb
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment data
    arr1: db "hello world this is a message to the world\0"
    arr2: db "this is not a message from the other world\0"
    "#);
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_eq!(e.flags.0 >> 32, 0);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    let arr1 = e.cpu.get_rsi();
    let arr2 = e.cpu.get_rdi();
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello world this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "this is not a message from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr1 + 1);
    assert_eq!(e.cpu.get_rdi(), arr2 + 1);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello world this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "hhis is not a message from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr1 + 21);
    assert_eq!(e.cpu.get_rdi(), arr2 + 21);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello world this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "hhis is not a mesis a from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr1 + 22);
    assert_eq!(e.cpu.get_rdi(), arr2 - 8);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello world this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "to the wnot a mesis a from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF));

    assert_eq!(e.execute_cycles(u64::MAX), (12, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr2 + 6);
    assert_eq!(e.cpu.get_rdi(), arr2 + 7);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello world this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "tttttttwnot a mesis a from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);
    assert_eq!(e.cpu.get_rcx(), 0);

    e.flags.set_ots();
    assert_eq!(e.execute_cycles(u64::MAX), (6, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr1 + 8);
    assert_eq!(e.cpu.get_rdi(), arr1 + 9);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hheell  old this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "tttttttwnot a mesis a from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_OTS));
    assert_eq!(e.cpu.get_rcx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (6, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr1 + 10);
    assert_eq!(e.cpu.get_rdi(), arr1 + 7);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hheell  old this a mageage the he worldrld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "tttttttwnot a mesis a from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_OTS | MASK_DF));
    e.flags.clear_ots();
    assert_eq!(e.cpu.get_rcx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (26, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr2 + 20);
    assert_eq!(e.cpu.get_rdi(), arr2 + 13);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hheell  old this a mageage the he worldrld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "tttttttwnot a r worler worler worler world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF));
    assert_eq!(e.cpu.get_rcx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr2 + 20);
    assert_eq!(e.cpu.get_rdi(), arr2 + 13);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hheell  old this a mageage the he worldrld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "tttttttwnot a r worler worler worler world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF));
    assert_eq!(e.cpu.get_rcx(), 0);

    e.flags.set_ots();
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rsi(), arr2 + 20);
    assert_eq!(e.cpu.get_rdi(), arr2 + 13);
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hheell  old this a mageage the he worldrld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "tttttttwnot a r worler worler worler world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_OTS | MASK_DF));
    assert_eq!(e.cpu.get_rcx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(0));
}
#[test]
fn test_stos() {
    let exe = asm_unwrap_link_unwrap!(r#"
    segment text
    mov rsi, arr1
    mov rdi, arr2
    hlt
    lea rdi, [arr1 + 7]
    mov rax, 0x41_62_43_64_45_66_47_68 ; AbCdEfGh
    cld
    stosb
    hlt
    lea rdi, [arr2 + 14]
    stosd
    hlt
    lea rdi, [arr1 + 24]
    std
    stosq
    hlt
    stosw
    hlt
    lea rdi, [arr2 + 3]
    cld
    mov ecx, 7
    rep stosb
    hlt
    lea rdi, [arr1 + 7]
    mov ecx, 17
    rep stosb
    hlt
    lea rdi, [arr1 + 35]
    std
    mov ecx, 5
    rep stosw
    hlt
    lea rdi, [arr2 + 34]
    mov ecx, 3
    rep stosq
    hlt
    lea rdi, [arr1 + 2]
    mov ecx, 0
    rep stosb
    hlt
    cld
    rep stosw
    hlt
    mov eax, sys_exit
    xor ebx, ebx
    syscall

    segment data
    arr1: db "hello world this is a message to the world\0"
    arr2: db "this is not a message from the other world\0"
    "#);
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_eq!(e.flags.0 >> 32, 0);
    let prev_flags = e.flags.0;

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    let arr1 = e.cpu.get_rsi();
    let arr2 = e.cpu.get_rdi();
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello world this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "this is not a message from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whrld this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "this is not a message from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);
    assert_eq!(e.cpu.get_rdi(), arr1 + 8);
    assert_eq!(e.cpu.get_rsi(), arr1);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whrld this is a message to the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "this is not a hGfEage from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);
    assert_eq!(e.cpu.get_rdi(), arr2 + 18);
    assert_eq!(e.cpu.get_rsi(), arr1);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whrld this is a mehGfEdCbA the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "this is not a hGfEage from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF));
    assert_eq!(e.cpu.get_rdi(), arr1 + 16);
    assert_eq!(e.cpu.get_rsi(), arr1);

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whrld thishGs a mehGfEdCbA the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "this is not a hGfEage from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF));
    assert_eq!(e.cpu.get_rdi(), arr1 + 14);
    assert_eq!(e.cpu.get_rsi(), arr1);

    assert_eq!(e.execute_cycles(u64::MAX), (12, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whrld thishGs a mehGfEdCbA the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "thihhhhhhht a hGfEage from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags);
    assert_eq!(e.cpu.get_rdi(), arr2 + 10);
    assert_eq!(e.cpu.get_rsi(), arr1);
    assert_eq!(e.cpu.get_rcx(), 0);

    e.flags.set_ots();
    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whhhhhhhhhhhhhhhhhhGfEdCbA the world".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "thihhhhhhht a hGfEage from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_OTS));
    assert_eq!(e.cpu.get_rdi(), arr1 + 24);
    assert_eq!(e.cpu.get_rsi(), arr1);
    assert_eq!(e.cpu.get_rcx(), 0);

    e.flags.clear_ots();
    assert_eq!(e.execute_cycles(u64::MAX), (10, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whhhhhhhhhhhhhhhhhhGfhGhGhGhGhGworld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "thihhhhhhht a hGfEage from the other world".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF));
    assert_eq!(e.cpu.get_rdi(), arr1 + 25);
    assert_eq!(e.cpu.get_rsi(), arr1);
    assert_eq!(e.cpu.get_rcx(), 0);

    e.flags.set_ots();
    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whhhhhhhhhhhhhhhhhhGfhGhGhGhGhGworld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "thihhhhhhht a hGfEhGfEdCbAhGfEdCbAhGfEdCbA".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF | MASK_OTS));
    assert_eq!(e.cpu.get_rdi(), arr2 + 10);
    assert_eq!(e.cpu.get_rsi(), arr1);
    assert_eq!(e.cpu.get_rcx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whhhhhhhhhhhhhhhhhhGfhGhGhGhGhGworld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "thihhhhhhht a hGfEhGfEdCbAhGfEdCbAhGfEdCbA".as_bytes());
    assert_eq!(e.flags.0, prev_flags | mask!(Flags: MASK_DF | MASK_OTS));
    assert_eq!(e.cpu.get_rdi(), arr1 + 2);
    assert_eq!(e.cpu.get_rsi(), arr1);
    assert_eq!(e.cpu.get_rcx(), 0);

    e.flags.clear_ots();
    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.memory.get_null_terminated(arr1).unwrap(), "hello whhhhhhhhhhhhhhhhhhGfhGhGhGhGhGworld".as_bytes());
    assert_eq!(e.memory.get_null_terminated(arr2).unwrap(), "thihhhhhhht a hGfEhGfEdCbAhGfEdCbAhGfEdCbA".as_bytes());
    assert_eq!(e.flags.0, prev_flags);
    assert_eq!(e.cpu.get_rdi(), arr1 + 2);
    assert_eq!(e.cpu.get_rsi(), arr1);
    assert_eq!(e.cpu.get_rcx(), 0);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(0));
}