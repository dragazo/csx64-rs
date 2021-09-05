use super::*;

#[test]
fn test_no_files() {
    let exe = asm_unwrap_link_unwrap!(std r#"
    global main
    segment text
    main: ret
    "#);
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    for handle in e.files.handles.iter() {
        assert!(handle.is_none()); // files should not be set up by default
    }
}

#[test]
fn test_fputc_putc_putchar() {
    let exe = asm_unwrap_link_unwrap!(std r#"
    global main
    extern fputc, putc, putchar
    extern stdout, stderr
    segment text
    main:
    
    mov rax, fputc
    mov rbx, putc
    hlt

    mov edi, 'g'
    mov rsi, stdout
    call fputc
    hlt

    mov edi, 'T'
    mov rsi, stderr
    call fputc
    hlt

    mov edi, 'P'
    mov esi, null ; just to make sure it's invalid for testing
    call putchar
    hlt

    mov eax, 42
    ret
    "#);
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let (_, stdout, stderr) = setup_standard_memory_streams(&mut e);
    
    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(e.cpu.get_rax(), e.cpu.get_rbx());
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "".as_bytes());

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "g".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "".as_bytes());
    assert_eq!(e.cpu.get_eax(), 'g' as u32);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "g".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "T".as_bytes());
    assert_eq!(e.cpu.get_eax(), 'T' as u32);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "gP".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "T".as_bytes());
    assert_eq!(e.cpu.get_eax(), 'P' as u32);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(42));
}

#[test]
fn test_fputs_puts() {
    let exe = asm_unwrap_link_unwrap!(std r#"
    global main
    extern fputs, puts
    extern stdout, stderr
    segment text
    main:
    
    mov rdi, $db("hello\n\tworld\0")
    mov rsi, stderr
    call fputs
    hlt

    mov rdi, $db("\0")
    mov rsi, stderr
    call fputs
    hlt

    mov rdi, $db("OwO\0oWo")
    mov rsi, stdout
    call fputs
    hlt

    mov rdi, $db("@ratings\0")
    mov esi, null ; just to make sure it's invalid for testing
    call puts
    hlt

    mov rdi, $db("\0")
    mov esi, null ; just to make sure it's invalid for testing
    call puts
    hlt

    mov eax, 42
    ret
    "#);
    let mut e = Emulator::new();
    e.init(&exe, &Default::default());
    assert_eq!(e.get_state(), State::Running);
    let (_, stdout, stderr) = setup_standard_memory_streams(&mut e);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "hello\n\tworld".as_bytes());
    assert_eq!(e.cpu.get_rax(), 12);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "hello\n\tworld".as_bytes());
    assert_eq!(e.cpu.get_rax(), 0);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "OwO".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "hello\n\tworld".as_bytes());
    assert_eq!(e.cpu.get_rax(), 3);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "OwO@ratings\n".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "hello\n\tworld".as_bytes());
    assert_eq!(e.cpu.get_rax(), 9);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "OwO@ratings\n\n".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "hello\n\tworld".as_bytes());
    assert_eq!(e.cpu.get_rax(), 1);

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(42));
}