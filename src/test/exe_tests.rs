use super::*;
use crate::asm::*;
use crate::exec::*;
use crate::exec::registers::Flags;

const ZSPACO: u64 = mask!(Flags: MASK_ZF | MASK_SF | MASK_PF | MASK_AF | MASK_CF | MASK_OF);

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
    
    let exe = assemble_and_link!(r"
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
    ".to_owned() => None).unwrap();
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let before_flags = e.get_flags().0;

    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x93f7a810f45e0e3c);
    assert_eq!(e.get_rbx(), 0x12de639fcd11a4cb);
    assert_eq!(e.get_rcx(), 0x046579a453add4b8);
    assert_eq!(e.get_rdx(), 0xfd221d7ea00b6846);
    assert_eq!(e.get_rsi(), 0xf1c89e98daa39a38);
    assert_eq!(e.get_rdi(), 0xbdb00d43f2aaff23);
    assert_eq!(e.get_rbp(), 0x949316d6a85099a0);
    assert_eq!(e.get_rsp(), 0xa228b0bd6d86600e);
    assert_eq!(e.get_r8(),  0x076899314a3e420b);
    assert_eq!(e.get_r9(),  0x05cc3887b130b66e);
    assert_eq!(e.get_r10(), 0x781b5ce0538f3fd0);
    assert_eq!(e.get_r11(), 0x2569467b20f81cb8);
    assert_eq!(e.get_r12(), 0xc0a9ed7647a335c4);
    assert_eq!(e.get_r13(), 0xf1570b21a8d728b5);
    assert_eq!(e.get_r14(), 0x65902d29eac939fb);
    assert_eq!(e.get_r15(), 0xec7aa569a6155ab1);
    assert_eq!(e.get_flags().0, before_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x000000007d22cbb4);
    assert_eq!(e.get_rbx(), 0x00000000becb162e);
    assert_eq!(e.get_rcx(), 0x00000000ae23158e);
    assert_eq!(e.get_rdx(), 0x000000000ddfe51b);
    assert_eq!(e.get_rsi(), 0x00000000a773170f);
    assert_eq!(e.get_rdi(), 0x00000000a71a36d7);
    assert_eq!(e.get_rbp(), 0x00000000d130b0c0);
    assert_eq!(e.get_rsp(), 0x0000000083b280d4);
    assert_eq!(e.get_r8(),  0x00000000a53b7121);
    assert_eq!(e.get_r9(),  0x0000000074c9e6d0);
    assert_eq!(e.get_r10(), 0x0000000058b7c4e7);
    assert_eq!(e.get_r11(), 0x00000000cabefe91);
    assert_eq!(e.get_r12(), 0x00000000aa92e8b4);
    assert_eq!(e.get_r13(), 0x0000000086bbdbc1);
    assert_eq!(e.get_r14(), 0x0000000079f4e348);
    assert_eq!(e.get_r15(), 0x00000000c023567e);
    assert_eq!(e.get_flags().0, before_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x000000007d22cb04);
    assert_eq!(e.get_rbx(), 0x00000000becb43f4);
    assert_eq!(e.get_rcx(), 0x00000000ae236493);
    assert_eq!(e.get_rdx(), 0x000000000ddfacd9);
    assert_eq!(e.get_rsi(), 0x00000000a773f019);
    assert_eq!(e.get_rdi(), 0x00000000a71a7d26);
    assert_eq!(e.get_rbp(), 0x00000000d13060f1);
    assert_eq!(e.get_rsp(), 0x0000000083b26476);
    assert_eq!(e.get_r8(),  0x00000000a53b3329);
    assert_eq!(e.get_r9(),  0x0000000074c909f4);
    assert_eq!(e.get_r10(), 0x0000000058b72cd7);
    assert_eq!(e.get_r11(), 0x00000000cabe6b08);
    assert_eq!(e.get_r12(), 0x00000000aa923644);
    assert_eq!(e.get_r13(), 0x0000000086bb217f);
    assert_eq!(e.get_r14(), 0x0000000079f4b5a4);
    assert_eq!(e.get_r15(), 0x00000000c0238df6);
    assert_eq!(e.get_flags().0, before_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (17, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x000000007d22cb1f);
    assert_eq!(e.get_rbx(), 0x00000000becb435d);
    assert_eq!(e.get_rcx(), 0x00000000ae236482);
    assert_eq!(e.get_rdx(), 0x000000000ddfacfb);
    assert_eq!(e.get_rsi(), 0x00000000a773f083);
    assert_eq!(e.get_rdi(), 0x00000000a71a7d78);
    assert_eq!(e.get_rbp(), 0x00000000d1306045);
    assert_eq!(e.get_rsp(), 0x0000000083b26408);
    assert_eq!(e.get_r8(),  0x00000000a53b33c6);
    assert_eq!(e.get_r9(),  0x0000000074c9095a);
    assert_eq!(e.get_r10(), 0x0000000058b72cd2);
    assert_eq!(e.get_r11(), 0x00000000cabe6b3e);
    assert_eq!(e.get_r12(), 0x00000000aa923687);
    assert_eq!(e.get_r13(), 0x0000000086bb2148);
    assert_eq!(e.get_r14(), 0x0000000079f4b594);
    assert_eq!(e.get_r15(), 0x00000000c0238d05);
    assert_eq!(e.get_flags().0, before_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x000000007d228c1f);
    assert_eq!(e.get_rbx(), 0x00000000becbae5d);
    assert_eq!(e.get_rcx(), 0x00000000ae23e182);
    assert_eq!(e.get_rdx(), 0x000000000ddfaffb);
    assert_eq!(e.get_flags().0, before_flags);
    
    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_r8(),  0x00000000a53b338c);
    assert_eq!(e.get_r9(),  0x0000000074c909ae);
    assert_eq!(e.get_r10(), 0x0000000058b72ce1);
    assert_eq!(e.get_r11(), 0x00000000cabe6baf);
    assert_eq!(e.get_flags().0, before_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0xfe630756u32 as i32)));
    assert_eq!(e.get_state(), State::Terminated(0xfe630756u32 as i32));

    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_mov() {
    let exe = assemble_and_link!(r"
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
    ".to_owned() => None).unwrap();
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let before_flags = e.get_flags().0;

    assert_eq!(e.execute_cycles(3), (3, StopReason::MaxCycles));
    assert_eq!(e.execute_cycles(u64::MAX), (8, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 12);
    assert_eq!(e.get_rbx(), 0xfffffffd);
    assert_eq!(e.get_rdi(), 2);
    assert_eq!(e.get_r8(), 22);
    assert_eq!(e.get_r9(), 0);
    assert_eq!(e.get_r10(), e.get_rdi());
    assert_eq!(e.get_mem_u32(e.get_r14()).unwrap(), 23);
    assert_eq!(e.get_mem_u32(e.get_r15()).unwrap(), e.get_ebx());
    assert_eq!(e.get_flags().0, before_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 3.14159f32.to_bits() as u64);
    assert_eq!(e.get_rbx(), 3.14159f64.to_bits());
    assert_eq!(e.get_flags().0, before_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::Terminated(54)));
    assert_eq!(e.get_state(), State::Terminated(54));
    assert_eq!(e.get_flags().0, before_flags);

    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_add() {
    let exe = assemble_and_link!(r"
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
    ".to_owned() => None).unwrap();
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x00000000ffff0015);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x00000000ffff0015);
    assert_eq!(e.get_rbx(), 0x00000000ffff0638);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF | MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 1);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 2);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!());

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 3);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_PF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x00000000ffffffef);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_SF));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x00000000fffffff0);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF | MASK_AF | MASK_CF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x0000000080000000);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF | MASK_OF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 16);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_AF));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}

#[test]
fn test_sub_cmp() {
    let exe = assemble_and_link!(r"
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
    ".to_owned() => None).unwrap();
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 3);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_PF));
    assert_eq!(get_conditions(e.get_flags()), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 3);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_SF | MASK_AF | MASK_CF));
    assert_eq!(get_conditions(e.get_flags()), ((true, true, false, false), (true, true, false, false)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 3);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_ZF | MASK_PF));
    assert_eq!(get_conditions(e.get_flags()), ((false, true, false, true), (false, true, false, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 1);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!());
    assert_eq!(get_conditions(e.get_flags()), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0xffff);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_SF | MASK_PF | MASK_AF | MASK_CF));
    assert_eq!(get_conditions(e.get_flags()), ((true, true, false, false), (true, true, false, false)));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x7fff);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_PF | MASK_AF | MASK_OF));
    assert_eq!(get_conditions(e.get_flags()), ((false, false, true, true), (true, true, false, false)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x7fff);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_PF));
    assert_eq!(get_conditions(e.get_flags()), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (2, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x7fff);
    assert_eq!(e.get_flags().0 & ZSPACO, mask!(Flags: MASK_PF));
    assert_eq!(get_conditions(e.get_flags()), ((false, false, true, true), (false, false, true, true)));

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(-1)));
    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}