use super::*;

#[test]
fn test_write() {
    let exe = asm_unwrap_link_unwrap!(r#"
    segment text
    mov eax, sys_write
    mov edi, 1 ; stdout
    mov rsi, $db("hello world\n\0hello")
    mov edx, 18
    syscall
    hlt
    xor rax, rax
    xor rdi, rdi
    syscall
    "#);
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_eq!(e.files.handles.len(), DEFAULT_MAX_FD);
    let (_, stdout, stderr) = setup_standard_memory_streams(&mut e);

    assert_eq!(e.execute_cycles(u64::MAX), (6, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 18);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "hello world\n\0hello".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "".as_bytes());
}
#[test]
fn test_read() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, sys_read
    mov edi, 0 ; stdin
    mov rsi, buf
    mov edx, buf.len
    syscall
    hlt
    mov rdx, rax
    mov eax, sys_write
    mov edi, 1 ; stdout
    syscall
    hlt
    xor rax, rax
    xor rdi, rdi
    syscall

    segment bss
    buf: resb 1024
    .len: equ $-buf
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    assert_eq!(e.files.handles.len(), DEFAULT_MAX_FD);
    let (stdin, stdout, stderr) = setup_standard_memory_streams(&mut e);
    stdin.lock().unwrap().content.get_mut().extend_from_slice("him name greg\n".as_bytes());

    assert_eq!(e.execute_cycles(u64::MAX), (6, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 14);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 14);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "him name greg\n".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "".as_bytes());
}

#[test]
fn test_brk() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, sys_brk
    mov edi, 0
    syscall
    hlt
    mov eax, sys_brk
    mov edi, 1
    syscall
    hlt
    mov eax, sys_brk
    lea rdi, [rbp - 1]
    syscall
    hlt
    mov eax, sys_brk
    mov rdi, !0
    syscall
    hlt
    mov eax, sys_brk
    mov rdi, rbp
    syscall
    hlt
    mov eax, sys_brk
    lea rdi, [rbp + 107]
    syscall
    hlt
    mov eax, sys_brk
    xor rdi, rdi
    syscall
    hlt
    mov eax, sys_brk
    lea rdi, [rbp + 66]
    syscall
    hlt
    mov eax, sys_brk
    lea rdi, [rbp - 1]
    syscall
    hlt
    xor rax, rax
    xor rdi, rdi
    syscall
    ");
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let base = e.cpu.get_rbp();

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), base);
    assert_eq!(e.memory.len() as u64, base);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), !0);
    assert_eq!(e.memory.len() as u64, base);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), !0);
    assert_eq!(e.memory.len() as u64, base);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), !0);
    assert_eq!(e.memory.len() as u64, base);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.memory.len() as u64, base);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.memory.len() as u64, base + 107);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), base + 107);
    assert_eq!(e.memory.len() as u64, base + 107);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 0);
    assert_eq!(e.memory.len() as u64, base + 66);

    assert_eq!(e.execute_cycles(u64::MAX), (4, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), !0);
    assert_eq!(e.memory.len() as u64, base + 66);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
}