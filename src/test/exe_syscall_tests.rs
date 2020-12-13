use super::*;
use crate::exec::*;
use crate::exec::fs::*;

use std::io::Cursor;
use std::sync::{Arc, Mutex};

type StdStream = Arc<Mutex<Cursor<Vec<u8>>>>;

fn setup_standard_memory_streams(e: &mut Emulator) -> (StdStream, StdStream, StdStream) {
    let stdin = Arc::new(Mutex::new(Cursor::new(vec![])));
    let stdout = Arc::new(Mutex::new(Cursor::new(vec![])));
    let stderr = Arc::new(Mutex::new(Cursor::new(vec![])));
    e.files.handles[0] = Some(Arc::new(Mutex::new(MemoryFile { content: stdin.clone(), readable: true, writable: false, seekable: false, interactive: true })));
    e.files.handles[1] = Some(Arc::new(Mutex::new(MemoryFile { content: stdout.clone(), readable: false, writable: true, seekable: false, interactive: false })));
    e.files.handles[2] = Some(Arc::new(Mutex::new(MemoryFile { content: stderr.clone(), readable: false, writable: true, seekable: false, interactive: false })));
    (stdin, stdout, stderr)
}

#[test]
fn test_write() {
    let exe = asm_unwrap_link_unwrap!(r#"
    segment text
    mov eax, sys_write
    mov ebx, 1 ; stdout
    mov rcx, $bin("hello world\n\0hello")
    mov edx, 18
    syscall
    hlt
    xor rax, rax
    xor rbx, rbx
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
    assert_eq!(stdout.lock().unwrap().get_ref(), "hello world\n\0hello".as_bytes());
    assert_eq!(stderr.lock().unwrap().get_ref(), "".as_bytes());
}
#[test]
fn test_read() {
    let exe = asm_unwrap_link_unwrap!(r"
    segment text
    mov eax, sys_read
    mov ebx, 0 ; stdin
    mov rcx, buf
    mov edx, buf.len
    syscall
    hlt
    mov rdx, rax
    mov eax, sys_write
    mov ebx, 1 ; stdout
    syscall
    hlt
    xor rax, rax
    xor rbx, rbx
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
    stdin.lock().unwrap().get_mut().extend_from_slice("him name greg\n".as_bytes());

    assert_eq!(e.execute_cycles(u64::MAX), (6, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 14);

    assert_eq!(e.execute_cycles(u64::MAX), (5, StopReason::ForfeitTimeslot));
    assert_eq!(e.cpu.get_rax(), 14);

    assert_eq!(e.execute_cycles(u64::MAX), (3, StopReason::Terminated(0)));
    assert_eq!(stdout.lock().unwrap().get_ref(), "him name greg\n".as_bytes());
    assert_eq!(stderr.lock().unwrap().get_ref(), "".as_bytes());
}