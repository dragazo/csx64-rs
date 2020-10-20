use super::*;
use crate::asm::*;
use crate::exec::*;

#[test]
fn test_imm_load() {
    
    let exe = assemble_and_link!(r"
    segment text
    mov rax, -7784568640113865156
    mov rbx, 0x12de639fcd11a4cbu
    mov rcx, 0x046579a453add4b8u
    mov rdx, 0o1764420727724002664106u
    mov rsi, 0xf1c89e98daa39a38u
    mov rdi, 0xbdb00d43f2aaff23u
    mov rbp, -7740818_22331708_3_744
    mov rsp, 0xa228b0bd6d86600eu
    mov r8, 0x076899314a3e420bu
    mov r9, 417771020883113582u
    mov r10, 0x781b5ce0538f3fd0u
    mov r11, 0x2569467b20f81cb8u
    mov r12, 0xc0a9ed7647a335c4u
    mov r13, 0o17052_7_0_262065_065_624_265u
    mov r14, 0x65902d29eac939fbu
    mov r15, 0xec7aa569a6155ab1u
    hlt
    mov eax, 0x7d22cbb4u
    mov ebx, 0xbecb162eu
    mov ecx, 0xae23158eu
    mov edx, 0x0ddfe51bu
    mov esi, 0o24_734_613_417u
    mov edi, 0xa71a36d7u
    mov ebp, 0xd130b0c0u
    mov esp, 2209513684u
    mov r8d, 0xa53b7121u
    mov r9d, 0x74c9e6d0u
    mov r10d, 0x58b7c4e7u
    mov r11d, 0b11001010101111101111111010010001u
    mov r12d, 0xaa92e8b4u
    mov r13d, 0x86bbdbc1u
    mov r14d, 0b_0111_1001_1111_0100_1110_0011_0100_1000u
    mov r15d, 0xc023567eu
    hlt
    mov ax, 0xcb04u
    mov bx, 0x43f4u
    mov cx, 0x6493u
    mov dx, 0xacd9u
    mov si, 0xf019u
    mov di, 32_038u
    mov bp, 0x60f1u
    mov sp, 0x6476u
    mov r8w, 0x3329u
    mov r9w, 0x09f4u
    mov r10w, 0x2cd7u
    mov r11w, 0x6b08u
    mov r12w, 0x3644u
    mov r13w, 0x217fu
    mov r14w, 0xb5a4u
    mov r15w, 0x8df6u
    hlt
    mov al, 0x1fu
    mov bl, 0x5du
    mov cl, 0x82u
    mov dl, 0xfbu
    mov sil, 0x83u
    mov dil, 0x78u
    mov bpl, 0x45u
    mov spl, 0x08u
    mov r8b, 0xc6u
    mov r9b, 0x5au
    mov r10b, 0xd2u
    mov r11b, 0x3eu
    mov r12b, 0x87u
    mov r13b, 0x48u
    mov r14b, 0x94u
    mov r15b, 0x05u
    hlt
    mov ah, 0x8cu
    mov bh, 0xaeu
    mov ch, 0xe1u
    mov dh, 0xafu
    hlt
    mov eax, 0u
    mov ebx, 0xfe630756u
    syscall
    times 256 nop
    ".to_owned() => None).unwrap();
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

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
    
    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.get_rax(), 0x000000007d228c1f);
	assert_eq!(e.get_rbx(), 0x00000000becbae5d);
	assert_eq!(e.get_rcx(), 0x00000000ae23e182);
    assert_eq!(e.get_rdx(), 0x000000000ddfaffb);
    
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

    mov edi, [dest1]
    mov esi, [dest2]
    mov eax, 0
    syscall
    times 50 nop

    segment rodata
    val: dd 22
    val2: dd 22u
    val3: dd 22.2
    segment bss
    align 4
    dest1: resd 1
    dest2: resd 1
    ".to_owned() => None).unwrap();
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);

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

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::Terminated(-3)));
    assert_eq!(e.get_state(), State::Terminated(-3));

    assert_eq!(e.execute_cycles(u64::MAX), (0, StopReason::NotRunning));
}