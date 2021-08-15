global atexit, exit, abort

segment text

; int atexit(void(*func)())
; adds func to the stack of functions to call in exit() before termination.
; the same function can be registered more than once.
; calls to atexit() during exit() will always fail.
; returns zero on success.
atexit:
    cmp byte ptr [exit_flag], 0
    jnz .fail ; calling atexit during exit always fails

    mov eax, [atexit_len]
    cmp eax, ATEXIT_CAP
    jae .fail ; check failure case (arr full)

    mov [atexit_arr + 8 * rax], rdi
    inc dword ptr [atexit_len]
    xor eax, eax ; return 0 (success)
    ret

    .fail:
    mov eax, 1
    ret

; [[noreturn]] void exit(int status)
; terminates execution with the specified status (return value).
; before termination, invokes all the functions set by (successful) calls to atexit() in reverse order.
; calling exit() from an atexit hook during exit() triggers an abort().
; it is recommended not to directly call sys_exit, as some of the atexit() cleanup may be important.
exit:
    cmp byte ptr [exit_flag], 0
    jnz abort ; calling exit during exit immediately kills with -1 result
    mov byte ptr [exit_flag], 1 ; set the exit flag

    ; we'll use call-safe registers - no need to preserve them since we won't be returning
    mov r15d, edi          ; status in r15d
    mov r14d, [atexit_len] ; len in r14
    
    jmp .aft
    .loop:
        call [atexit_arr + 8 * r14]
    .aft:
        dec r14
        cmp r14, 0
        jge .loop

    .done:
    mov eax, sys_exit
    mov edi, r15d
    syscall

; void abort(void);
; immediately terminates execution with error code -1.
; it is recommended to use exit() instead where possible, as abort performs no cleanup.
abort:
    mov eax, sys_exit
    mov edi, -1
    syscall

segment bss

ATEXIT_CAP: equ 32 ; atexit static capacity - must be at least 32

align 8
atexit_arr: resq ATEXIT_CAP
atexit_len: resd 1
exit_flag: resb 1
