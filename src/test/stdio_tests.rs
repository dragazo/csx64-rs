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
    mov esi, stdout
    call fputc
    hlt

    mov edi, 'T'
    mov esi, stderr
    call fputc
    hlt

    mov edi, 'P'
    mov esi, null ; just to make sure it's invalid
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

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "g".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "T".as_bytes());

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::ForfeitTimeslot);
    assert_eq!(stdout.lock().unwrap().content.get_ref(), "gP".as_bytes());
    assert_eq!(stderr.lock().unwrap().content.get_ref(), "T".as_bytes());

    assert_eq!(e.execute_cycles(u64::MAX).1, StopReason::Terminated(42));
}