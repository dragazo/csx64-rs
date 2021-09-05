; source http://www.cplusplus.com/reference/cstdio/
; needs a TON of file handling code

; --------------------------------------

global stdin, stdout, stderr

; --------------------------------------

; global remove, rename

; --------------------------------------

global fputc, putc, putchar
global fputs, puts
; global fwrite

; global scanf, vscanf
; global fscanf, vfscanf

; global printf, vprintf
; global fprintf, vfprintf
; global sprintf, vsprintf
; global snprintf, vsnprintf

; --------------------------------------

; global ungetc, fgetc, getchar, fpeek

; --------------------------------------

; global fopen, fflush, fclose

; --------------------------------------

extern arglist_start, arglist_end
extern arglist_i, arglist_f

extern malloc, free
extern strlen
extern isspace

; --------------------------------------

segment text

FILE:
    .ALIGN:     equ 4
    .SIZE:      equ 12
    
    .fd:        equ 0 ; int (connected (open) file descriptor from native platform)
    .ungetc_ch: equ 4 ; int (character put back into stream by ungetc - only 1 allowed - EOF (-1) for none)
    .static:    equ 8 ; int (bool flag marking as static object (no free()) - e.g. stdout)

; --------------------------------------

; ; int remove(const char *path);
; remove:
;     mov eax, sys_unlink
;     mov rbx, rdi
;     syscall
;     ret

; ; int rename(const char *from, const char *to);
; rename:
;     mov eax, sys_rename
;     mov rbx, rdi
;     mov rcx, rsi
;     syscall
;     ret
    
; --------------------------------------

; int putchar(int ch)
putchar:
    mov rsi, stdout
; int fputc(int ch, FILE *stream)
; int putc(int ch, FILE *stream)
fputc:
putc:
    mov byte ptr [rsp - 1], dil ; put ch in memory so it has an address
    mov ebx, edi ; save ch for later

    ; write the character (string of length 1)
    mov eax, sys_write
    mov edi, dword ptr [rsi + FILE.fd]
    lea rsi, [rsp - 1]
    mov edx, 1
    syscall
    
    ; if that failed (-1), return EOF (-1), otherwise the written char
    cmp rax, -1
    cmovne eax, ebx
    static_assert EOF == -1 ; we're using this fact to avoid a mov
    ret

; int fputs(const char *str, FILE *stream)
fputs:
    ; get the string length
    push rdi
    push rsi
    call strlen
    
    ; write the string
    pop rdi
    pop rsi
    mov edi, dword ptr [edi + FILE.fd]
    mov rdx, rax
    mov eax, sys_write
    syscall
    
    ret ; return the number of characters written (returned from native call)
; int puts(const char *str)
puts:
    mov rsi, stdout
    call fputs
    cmp eax, EOF
    je .ret

    .ok:
    push eax
    mov edi, '\n'
    call putchar ; puts() also adds a new line char after string - c stdlib is weird
    pop eax

    mov ebx, eax ; add one char to #written if putchar succeeded
    inc ebx
    cmovnz eax, ebx

    .ret: ret
    
; ; size_t fwrite(const void *ptr, size_t size, size_t count, FILE *stream)
; fwrite:
;     ; if size or count is zero, no-op
;     cmp rsi, 0
;     je .nop
;     cmp rdx, 0
;     je .nop
    
;     ; otherwise write the block
;     mov eax, sys_write
;     mov ebx, dword ptr [rcx + FILE.fd]
;     mov rcx, rdi
;     imul rdx, rsi
;     syscall
    
;     ; return number of successes (rax holds number of bytes written from native call)
;     xor rdx, rdx
;     div rsi ; quotient stored in rax
;     ret
    
;     .nop: ; nop case returns zero and does nothing else
;     xor rax, rax
;     ret

; --------------------------------------

; the following formatting functions implicitly take a creader function in r15.
; the creader function takes the form int(*)(int), examining and returning the next character in the stream.
; if no more chars are available, EOF should be returned and all subsequent calls should do likewise.
; if the argument is nonzero, the character is extracted, otherwise it should remain in the stream for future calls.
; the creader function itself is allowed to store an argument in r14.
; as a contract, you should not modify the values of r14,r15 if you intend to use the creader function.

; int __scanf_u64_decimal(u64 *dest)
; reads a u64 value from the stream and stores it in dest.
; returns nonzero on success.
; __scanf_u64_decimal:
;     push r12 ; save this call-safe register (holds working value)
;     push r13 ; save this call-safe register as well (holds the iteration index)
;     push rdi ; save dest on the stack
    
;     xor r12, r12 ; zero the working value
;     xor r13, r13 ; zero iteration index

;     .top:
;         xor edi, edi
;         call r15 ; peek the next character from the stream
        
;         ; if it's not a digit, break from the loop
;         sub eax, '0' ; convert to binary
;         cmp eax, 9
;         ja .brk ; unsigned compare avoids having to test negative bounds as well
        
;         ; otherwise extract the character from the stream
;         mov edi, 1
;         call r15
;         sub eax, '0'
        
;         ; fold in the digit
;         xchg rax, r12
;         mul qword 10
;         jc .fail ; check for overflow from the multiply
;         add r12, rax
;         jc .fail ; check for overflow from the add
        
;         inc r13
;         jmp .top
;     .brk:
    
;     ; if we failed on the first iteration, fail
;     cmp r13, 0
;     jz .fail
    
;     pop rax
;     mov qword ptr [rax], r12 ; store the result to dest
;     pop r13
;     pop r12
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     pop r13
;     pop r12
;     xor eax, eax ; return false
;     ret
; ; int __scanf_i64_decimal(i64 *dest)
; ; reads an i64 value from the strem and stores it in dest.
; ; returns nonzero on success.
; __scanf_i64_decimal:
;     push rdi ; save dest
    
;     xor edi, edi
;     call r15 ; peek the next char in the stream
    
;     cmp eax, '+'
;     je .sign
;     cmp eax, '-'
;     je .sign
;     push dword '+' ; if no explicit sign char, put a + on the stack (see .sign)
;     jmp .aft_sign
    
;     .sign:
;     mov edi, 1
;     call r15 ; extract the sign character
;     push eax ; store it on the stack
;     .aft_sign:
    
;     sub rsp, 8 ; create space for storing intermediate parse result
;     mov rdi, rsp
;     call __scanf_u64_decimal ; read the numeric value (store on stack)
;     pop rdx ; pop the result off the stack immediately
;     cmp eax, 0
;     jnz .u64_success ; if that failed (zero) we fail as well (zero)
;     add rsp, 4+8 ; remove stack space for dest and sign character
;     ret
;     .u64_success:
    
;     pop eax ; pop the sign character off the stack
;     cmp eax, '-'
;     jne .aft_sign_fix
;     neg rdx
;     js .aft_sign_fix ; if result is negative, we didn't overflow
;     pop rax
;     xor eax, eax ; otherwise fail - return false
;     ret
;     .aft_sign_fix:
    
;     pop rax ; pop dest off the stack
;     mov qword ptr [rax], rdx ; store the final result to dest
;     mov eax, 1 ; return true
;     ret

; ; int __scanf_u32_decimal(u32 *dest)
; __scanf_u32_decimal:
;     push rdi ; store dest
;     sub rsp, 8
;     mov rdi, rsp
;     call __scanf_u64_decimal ; parse a u64 value and put on stack
;     pop rbx ; pop the result off the stack immediately
;     cmp eax, 0
;     jz .fail ; if that failed, we fail as well
    
;     mov eax, ebx
;     cmp rax, rbx
;     jne .fail ; if the value cannot be represented as a u32, fail
    
;     pop rdi
;     mov dword ptr [rdi], eax
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     xor eax, eax ; return false
;     ret
; ; int __scanf_u16_decimal(u16 *dest)
; __scanf_u16_decimal:
;     push rdi ; store dest
;     sub rsp, 8
;     mov rdi, rsp
;     call __scanf_u64_decimal ; parse a u64 value and put on stack
;     pop rbx ; pop the result off the stack immediately
;     cmp eax, 0
;     jz .fail ; if that failed, we fail as well
    
;     movzx eax, bx
;     cmp rax, rbx
;     jne .fail ; if the value cannot be represented as a u32, fail
    
;     pop rdi
;     mov word ptr [rdi], ax
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     xor eax, eax ; return false
;     ret
; ; int __scanf_u8_decimal(u8 *dest)
; __scanf_u8_decimal:
;     push rdi ; store dest
;     sub rsp, 8
;     mov rdi, rsp
;     call __scanf_u64_decimal ; parse a u64 value and put on stack
;     pop rbx ; pop the result off the stack immediately
;     cmp eax, 0
;     jz .fail ; if that failed, we fail as well
    
;     movzx eax, bl
;     cmp rax, rbx
;     jne .fail ; if the value cannot be represented as a u32, fail
    
;     pop rdi
;     mov byte ptr [rdi], al
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     xor eax, eax ; return false
;     ret

; ; int __scanf_i32_decimal(i32 *dest)
; __scanf_i32_decimal:
;     push rdi ; store dest
;     sub rsp, 8
;     mov rdi, rsp
;     call __scanf_i64_decimal ; parse an i64 value and put on stack
;     pop rbx ; pop the result off the stack immediately
;     cmp eax, 0
;     jz .fail ; if that failed, we fail as well
    
;     movsx rax, ebx
;     cmp rax, rbx
;     jne .fail ; if the value cannot be represented as a u32, fail
    
;     pop rdi
;     mov dword ptr [rdi], eax
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     xor eax, eax ; return false
;     ret
; ; int __scanf_i16_decimal(i16 *dest)
; __scanf_i16_decimal:
;     push rdi ; store dest
;     sub rsp, 8
;     mov rdi, rsp
;     call __scanf_i64_decimal ; parse an i64 value and put on stack
;     pop rbx ; pop the result off the stack immediately
;     cmp eax, 0
;     jz .fail ; if that failed, we fail as well
    
;     movsx rax, bx
;     cmp rax, rbx
;     jne .fail ; if the value cannot be represented as a u32, fail
    
;     pop rdi
;     mov word ptr [rdi], ax
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     xor eax, eax ; return false
;     ret
; ; int __scanf_i8_decimal(i8 *dest)
; __scanf_i8_decimal:
;     push rdi ; store dest
;     sub rsp, 8
;     mov rdi, rsp
;     call __scanf_i64_decimal ; parse an i64 value and put on stack
;     pop rbx ; pop the result off the stack immediately
;     cmp eax, 0
;     jz .fail ; if that failed, we fail as well
    
;     movsx rax, bl
;     cmp rax, rbx
;     jne .fail ; if the value cannot be represented as a u32, fail
    
;     pop rdi
;     mov byte ptr [rdi], al
;     mov eax, 1 ; return true
;     ret
    
;     .fail:
;     pop rax
;     xor eax, eax ; return false
;     ret
    
; ; void __scanf_skipws(void)
; ; skips white space characters as if by calling isspace().
; __scanf_skipws:
;     xor edi, edi
;     call r15 ; peek the next char in the stream
    
;     mov edi, eax
;     call isspace
;     cmp eax, 0
;     jz .nonspace ; if it's not space, we're done
    
;     ; otherwise extract the char from the stream and repeat
;     mov edi, 1
;     call r15
;     jmp __scanf_skipws
    
;     .nonspace:
;     ret
    
; ; int __vscanf(const char *fmt, arglist *args, creader : r15, creader_arg : r14)
; ; this serves as the implementation for all the various scanf functions.
; ; the format string and arglist should be passed as normal args.
; ; the arglist should already be advanced to the location of the first arg to store scan results to.
; ; the creader function and creader arg should be set up in registers r14 and r15
; __vscanf:
;     sub rsp, 32
;     mov qword ptr [rsp + 0], rdi
;     mov qword ptr [rsp + 8], rsi
;     mov qword ptr [rsp + 16], r12 ; r12 will point to the character being processed in format string
;     mov qword ptr [rsp + 24], r13 ; r13 will hold the total number of successful parse actions
    
;     mov r12, rdi ; point r12 at the first character to process in the format string
;     xor r13, r13 ; clear the number of successful actions
    
;     jmp .loop_test
;     .loop_body:
;         cmp al, '%'
;         jne .literal_char
;         inc r12 ; skip to next char (format flag)
;         mov al, byte ptr [r12] ; get the following character
;         cmp al, 0
;         jz .loop_break ; if it's a terminator, just break from the loop
        
;         cmp al, 'd'
;         je .i32_decimal
;         cmp al, 'u'
;         je .u32_decimal
;         cmp al, '%'
;         je .literal_nonwhite ; %% escape sequence
        
;         ; otherwise unknown format flag
;         mov rdi, $str(`\n[[ERROR]] unrecognized scanf format flag\n`)
;         mov rsi, stderr
;         call fputs
;         jmp .loop_break
        
;         .i32_decimal:
;         call __scanf_skipws ; this format flag implicitly skips white space before parsing
;         mov rdi, qword ptr [rsp + 8] ; load the arglist
;         call arglist_i ; get the next parse destination (pointer)
;         mov rdi, rax
;         call __scanf_i32_decimal ; parse the next i32 value into that location
;         cmp eax, 0
;         jz .loop_break ; if that failed, abort parsing
;         inc r13 ; bump up the number of successful parse actions
;         jmp .loop_aft
        
;         .u32_decimal:
;         call __scanf_skipws ; this format flag implicitly skips white space before parsing
;         mov rdi, qword ptr [rsp + 8] ; load the arglist
;         call arglist_i ; get the next parse destination (pointer)
;         mov rdi, rax
;         call __scanf_u32_decimal ; parse the next i32 value into that location
;         cmp eax, 0
;         jz .loop_break ; if that failed, abort parsing
;         inc r13 ; bump up the number of successful parse actions
;         jmp .loop_aft
        
;         .literal_char: ; this is anything other than '%'
;         movzx edi, al
;         call isspace
;         cmp eax, 0
;         jz .literal_nonwhite
;         call __scanf_skipws ; if it's a white space char, skip white space in the stream
;         jmp .loop_aft
;         .literal_nonwhite:
        
;         ; otherwise we need to match a character
;         xor edi, edi
;         call r15 ; peek the next character in the stream
;         movzx ebx, byte ptr [r12] ; reload the char since we clobbered it
;         cmp eax, ebx
;         jne .loop_break ; if they differ, abort parsing
;         mov edi, 1
;         call r15 ; otherwise extract the character from the stream
;     .loop_aft:
;         inc r12
;     .loop_test:
;         mov al, byte ptr [r12] ; read the next char in format string
;         cmp al, 0
;         jnz .loop_body
;     .loop_break:
    
;     mov rax, r13 ; return number of successful parse actions
;     mov r12, qword ptr [rsp + 16]
;     mov r13, qword ptr [rsp + 24]
;     add rsp, 32
;     ret

; ; --------------------------------------

; ; int vfscanf(FILE *stream, const char *fmt, arglist *args)
; vfscanf:
;     push r14
;     push r15
    
;     mov r14, rdi
;     mov rdi, rsi
;     mov rsi, rdx
;     mov r15, .__CREADER
;     call __vscanf
    
;     pop r15
;     pop r14
;     ret
    
;     .__CREADER:
;         cmp edi, 0
;         mov rdi, r14
;         jz fpeek
;         jmp fgetc
; ; int fscanf(FILE *stream, const char *fmt, ...)
; fscanf:
;     mov r10, rsp
;     push r15
;     call arglist_start
;     push rax
;     push rsi
;     push rdi
;     mov rdi, rax
;     times 2 call arglist_i
    
;     mov rdx, rdi
;     pop rdi
;     pop rsi
;     call vfscanf
;     mov r15, rax
    
;     pop rdi
;     call arglist_end
;     mov rax, r15
;     pop r15
;     ret

; ; int vscanf(const char *fmt, arglist *args)
; vscanf:
;     mov rdx, rsi
;     mov rsi, rdi
;     mov rdi, stdin
;     jmp vfscanf
; ; int scanf(const char *fmt, ...)
; scanf:
;     mov r10, rsp
;     push r15
;     call arglist_start
;     push rax
;     push rdi
;     mov rdi, rax
;     call arglist_i
    
;     mov rsi, rdi
;     pop rdi
;     call vscanf
;     mov r15, rax
    
;     pop rdi
;     call arglist_end
;     mov rax, r15
;     pop r15
;     ret

; --------------------------------------
    
; printf format flag (prefix) enum
__vprintf_fmt: equ 0
    .minus: equ 1   ; - flag was used (left justify)
    .plus:  equ 2   ; + flag was used (showpos)
    .hash:  equ 4   ; # flag was used (showbase/showpoint depending on int/float)
    .zero:  equ 8   ; 0 flag was used (pad with zeros)
    .width: equ 16  ; width was specified (most things ignore this)
    .prec:  equ 32  ; precision was specified (most things ignore this)

__vprintf_scale: equ 0
    .default: equ 0
    .hh:      equ 1
    .h:       equ 2
    .l:       equ 3
    .ll:      equ 4
    .j:       equ 5
    .z:       equ 6
    .t:       equ 7
    .L:       equ 8
    
    .COUNT: equ 9 ; the number of enum values
    
__vprintf_fmt_pack: equ 0
    .SIZE: equ 16
    
    .fmt:   equ 0  ; u32 collection of format flags
    .width: equ 4  ; u32 width to use (positive)
    .prec:  equ 8  ; u32 precision to use (positive)
    .scale: equ 12 ; u32 denotes size of operand

; int __vprintf_read_prefix(fmt_pack *res : rsi, arglist * : r10, const char *&str : r12);
; WARNING: nonstandard calling convention.
; reads all the relevant formatting info for the current item (after reading the % char).
; returns zero on success.
; __vprintf_read_prefix:
;     xor ecx, ecx ; clear ecx (will hold flags)
    
;     .unord_flag_loop:
;         mov al, byte ptr [r12]
        
;         cmp al, '+'
;         je .plus
;         cmp al, '-'
;         je .minus
;         cmp al, '0'
;         je .zero
;         cmp al, '#'
;         je .hash
        
;         jmp .unord_flag_loop_done ; if it was none of those, we're done
        
;         .plus:
;             test ecx, __vprintf_fmt.plus ; test if this flag was already set (if so, invalid fmt)
;             jnz .invalid
;             or ecx, __vprintf_fmt.plus
;             jmp .unord_flag_aft
;         .minus:
;             test ecx, __vprintf_fmt.minus ; test if this flag was already set (if so, invalid fmt)
;             jnz .invalid
;             or ecx, __vprintf_fmt.minus
;             jmp .unord_flag_aft
;         .zero:
;             test ecx, __vprintf_fmt.zero ; test if this flag was already set (if so, invalid fmt)
;             jnz .invalid
;             or ecx, __vprintf_fmt.zero
;             jmp .unord_flag_aft
;         .hash:
;             test ecx, __vprintf_fmt.hash ; test if this flag was already set (if so, invalid fmt)
;             jnz .invalid
;             or ecx, __vprintf_fmt.hash
            
;     .unord_flag_aft:
;         inc r12 ; on to next char
;         jmp .unord_flag_loop
;     .unord_flag_loop_done:
    
;     xor eax, eax ; clear eax (will hold width)
;     mov bl, byte ptr [r12] ; read the next char
;     cmp bl, '*'
;     je .param_width ; if char is * then width is specified via param
;     sub bl, '0'
;     cmp bl, 10
;     jae .no_width ; if it's not a digit then there's no width specified
    
;     or ecx, __vprintf_fmt.width ; mark that a width was specified
;     inc r12    ; increment up to the next char
;     mov al, bl ; move the 0-9 first digit into the width register
;     .width_parsing:
;         movzx ebx, byte ptr [r12] ; read the next character from format string
;         sub bl, '0'
;         cmp bl, 10
;         jae .width_parsing_done ; if it's not a digit, we're done parsing width
        
;         imul eax, 10 ; incorporate the next digit into the width value
;         add eax, ebx
;         inc r12
;         jmp .width_parsing
;     .width_parsing_done:
;     jmp .no_width ; resume logic after width parsing
    
;     .param_width:
;     inc r12 ; increment up to the next char
;     or ecx, __vprintf_fmt.width ; mark that a width was specified
;     mov r11, rdi     ; save rdi in r11 for the main __vprintf func
;     mov rdi, r10     ; load the arglist pointer
;     call arglist_i   ; get a 32-bit integer arg from the pack and use it as width
;     mov rdi, r11
;     cmp eax, 0
;     movl eax, 0 ; if prec is negative, set it to zero
    
;     .no_width:
;     mov dword ptr [rsi + __vprintf_fmt_pack.width], eax ; store the width in the format pack
    
;     xor eax, eax ; clear eax (will hold precision)
;     cmp byte ptr [r12], '.'
;     jne .no_prec ; if next char is not a . then there's no precision
    
;     or ecx, __vprintf_fmt.prec ; mark that a precision was specified
;     inc r12 ; skip the .
    
;     mov bl, byte ptr [r12] ; read the first character of precision field from format string
;     cmp bl, '*'
;     je .param_prec ; if it's a * then we use a param precision value
;     sub bl, '0'
;     cmp bl, 10
;     jae .invalid ; if it's not a digit then this format string is invalid
    
;     inc r12    ; increment up to the next char
;     mov al, bl ; move the 0-9 first digit into the width register
;     .prec_parsing:
;         movzx ebx, byte ptr [r12] ; read the next character from format string
;         sub bl, '0'
;         cmp bl, 10
;         jae .prec_parsing_done ; if it's not a digit, we're done parsing precision
        
;         imul eax, 10 ; incorporate the next digit into the precision value
;         add eax, ebx
;         inc r12
;         jmp .prec_parsing
;     .prec_parsing_done:
;     jmp .no_prec ; resume logic after prec parsing
    
;     .param_prec:
;     inc r12 ; bump up to the next character
;     mov r11, rdi     ; save rdi in r11 for the main __vprintf func
;     mov rdi, r10     ; load the arglist pointer
;     call arglist_i   ; get a 32-bit integer arg from the pack and use it as precision
;     mov rdi, r11
;     cmp eax, 0
;     movl eax, 0 ; if prec is negative, set it to zero
    
;     .no_prec:
;     mov dword ptr [rsi + __vprintf_fmt_pack.prec], eax ; store the precision in the format pack
    
;     mov bl, byte ptr [r12] ; read the next char of the format string
;     cmp bl, 'h'
;     je .half_seq ; if it's an h we're in h or hh case (short/char)
;     cmp bl, 'l'
;     je .long_seq ; if it's an l we're in l or ll case (long/long long)
;     cmp bl, 'j'
;     je .j_scale ; if it's a j we're in intmax case
;     cmp bl, 'z'
;     je .z_scale ; if it's a z we're in size_t case
;     cmp bl, 't'
;     je .t_scale ; if it's a t we're in ptrdiff_t case
;     cmp bl, 'L'
;     je .L_scale ; if it's an L we're in long double case
    
;     mov eax, __vprintf_scale.default ; otherwise use the default option and continue (no chars to extract)
;     jmp .scale_done
    
;     .L_scale:
;     mov eax, __vprintf_scale.L
;     inc r12 ; move to next char in format string
;     jmp .scale_done
    
;     .t_scale:
;     mov eax, __vprintf_scale.t
;     inc r12 ; move to next char in format string
;     jmp .scale_done
    
;     .z_scale:
;     mov eax, __vprintf_scale.z
;     inc r12 ; move to next char in format string
;     jmp .scale_done
    
;     .j_scale:
;     mov eax, __vprintf_scale.j
;     inc r12 ; move to next char in format string
;     jmp .scale_done
    
;     .half_seq:
;     mov eax, __vprintf_scale.h
;     inc r12 ; move to next char in format string
;     cmp byte ptr [r12], 'h'
;     jne .scale_done ; if it's not another h we're done with scale
;     mov eax, __vprintf_scale.hh
;     inc r12 ; consume the second h as well
;     jmp .scale_done
    
;     .long_seq:
;     mov eax, __vprintf_scale.l
;     inc r12 ; move to next char in format string
;     cmp byte ptr [r12], 'l'
;     jne .scale_done ; if it's not another l we're done with scale
;     mov eax, __vprintf_scale.ll
;     inc r12 ; consume the second l as well
    
;     .scale_done:
;     mov dword ptr [rsi + __vprintf_fmt_pack.scale], eax ; store scale info to format pack
    
;     mov dword ptr [rsi + __vprintf_fmt_pack.fmt], ecx ; and finally, store the format flags to the format pack as well
    
;     xor eax, eax ; return 0
;     ret ; finally done - pack fully parsed and r12 now points to the mode character
    
;     .invalid: ; this happens if the format string was invalid (failed to parse)
;     mov eax, 1
;     ret ; return nonzero to indicate failure

; the following formatting functions implicitly take a sprinter function in r15.
; the sprinter function takes the form u64(*)(const char*), printing the string and returning # chars written.
; the sprinter function itself is allowed to store an argument in r14.
; as a contract, you should not modify the values of r14,r15 if you intend to use the sprinter function.

; u64 __printf_u64_raw(u64 val, __vprintf_fmt_pack *fmt, bool neg : bl, u64 radix : rcx, char alpha_base : bh)
; WARNING: nonstandard calling convention
; prints the (unsigned) value and returns the number of characters written to the stream
; __printf_u64_raw:
;     mov r10d, dword ptr [rsi + __vprintf_fmt_pack.width]
;     mov r11d, dword ptr [rsi + __vprintf_fmt_pack.prec]
;     cmp r11d, r10d
;     movg r10d, r11d ; put larger of width/precision in r10d
;     and r10d, ~7 ; round down to a multiple of 8
;     add r10d, 32 ; add some more to still be a multiple of 8 but also have extra space for '-' and base prefixes
    
;     mov rax, rsp
;     sub rsp, r10 ; allocate that many bytes on the stack
;     push rax     ; save original value of rsp on the stack for restore point later
    
;     lea r8, [rsp+8 + r10 - 1] ; r8 points to the start of the string
;     mov byte ptr [r8], 0      ; place a null terminator at end of string
    
;     mov rax, rdi ; put the value in rax for division
;     .loop_top:
;         xor rdx, rdx ; zero high bits for division
;         div rcx ; divide by radix - quot kept in rax, remainder (next digit) stored in rdx
        
;         sub dl, 10         ; subtract/compare to 10
;         jae .alpha_char    ; if it was 10 or higher, convert to alpha using alpha_base
;         add dl, 10 + '0'   ; otherwise add back the 10 and convert to a digit
;         jmp .char_finished ; and now this char is properly formatted
;         .alpha_char:
;         add dl, bh         ; if it's alpha, add alpha_base (bh)
;         .char_finished:
        
;         dec r8                ; make room for another character
;         mov byte ptr [r8], dl ; place the ascii char into the string
        
;         cmp rax, 0
;         jnz .loop_top ; if quotient was nonzero repeat
    
;     ; cl holds the radix (used below for showbase logic)
;     mov ch, 0 ; ch will hold the sign character (0 for none)
;     cmp bl, 0 ; test the neg flag parameter
;     movnz ch, '-'
;     jnz .no_sign ; if (-) flag was true, we use '-' char
;     cmp al, 10
;     jne .no_sign ; otherwise, if not in decimal mode we don't print '+' sign regardless of if + flag was specified
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.plus ; check if plus flag is set in format pack
;     movnz ch, '+'
;     .no_sign:
    
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.prec
;     jnz .done_prec_fetch ; if a precedence was explicitly specified, use that (already in r11)
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.zero
;     jz .prec_done ; otherwise if the zero flag was not specified, we can just entirely skip the prec logic
;     mov r11d, dword ptr [rsi + __vprintf_fmt_pack.width] ; otherwise use width
;     cmp ch, 0
;     setnz rdx
;     sub r11, rdx ; subtract 1 if there's going to be a sign character
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.hash
;     jz .done_prec_fetch ; if showbase is disabled, we're done with prec computation
;         cmp cl, 16
;         je .prec_hex ; if in hex mode
;         cmp cl, 8
;         sete rdx
;         sub r11, rdx ; otherwise, if in octal mode, take off 1 char for 0 prefix
;         jmp .done_prec_fetch
;         .prec_hex:
;         sub r11, 2 ; take off 2 chars from precision for the 0x prefix
;     .done_prec_fetch:
    
;     lea r9, [rsp+8 + r10 - 1] ; load the address of the terminator
;     sub r9, r11               ; subtract precision - this is address to which we should get with digits
;     jmp .prec_test
;     .prec_top:
;         dec r8                 ; make room for another char
;         mov byte ptr [r8], '0' ; place a zero in the string
;     .prec_test:
;         cmp r8, r9
;         ja .prec_top
;     .prec_done:
    
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.hash ; check if the hash flag was specified in the format string
;     jz .noshowbase ; if it wasn't specified, skip showbase logic
;     cmp cl, 16
;     je .showbase_hex   ; if base was 16, print hex prefix
;     cmp cl, 8
;     je .showbase_octal ; if base was 8, print octal prefix
;     jmp .noshowbase    ; otherwise no prefix
;     .showbase_octal:
;         dec r8
;         mov byte ptr [r8], '0' ; append '0' to string
;         jmp .noshowbase
;     .showbase_hex:
;         dec r8
;         mov byte ptr [r8], bh
;         add byte ptr [r8], 'x'-'a' ; append 'x' to string (based on alpha base to support uppercase)
;         dec r8
;         mov byte ptr [r8], '0' ; append '0' to string
;     .noshowbase:
    
;     cmp ch, 0
;     jz .no_sign_print
;     dec r8                ; make room for another character
;     mov byte ptr [r8], ch ; add the sign character to the string
;     .no_sign_print:
    
;     mov r11d, dword ptr [rsi + __vprintf_fmt_pack.width]
;     lea r9, [rsp+8 + r10 - 1] ; load the address of the terminator
;     sub r9, r8                ; subtract string start - this is current length of string
;     mov rbx, r11
;     sub rbx, r9 ; rbx holds width - current len i.e. the number of spaces to add
    
;     mov rdi, r8 ; put string start in rdi (after padding logic, it needs to be there)
;     cmp r9, r11
;     jae .done ; if we've already passed the width requirement, we're done
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.minus
;     jz .right_justify
    
;     mov rcx, r9 ; put current length of string in rcx
;     mov rsi, r8 ; source is start of string
;     mov rdi, r8
;     sub rdi, rbx ; dest is start of string - number of spaces to add
;     mov r10, rdi ; save dest in r10 for later (see below)
    
;     cld       ; clear direction flag so we can do a forward copy
;     rep movsb ; copy the string to the left
    
;     mov rcx, rbx ; set the number of spaces to insert
;     mov al, ' '  ; set the fill character
    
;     rep stosb ; insert that many spaces to the right of the string
    
;     mov rdi, r10 ; load the the start of string (see above)
;     jmp .done    ; and now we're done padding
    
;     .right_justify:
;     mov rcx, rbx ; set number of chars to insert
;     mov al, ' '  ; set padding char
;     mov rdi, r8
;     dec rdi      ; dest is 1 before start of string
;     std          ; set direction flag so we perform the insertion right-to-left
;     rep stosb    ; insert the padding chars
;     inc rdi      ; since count was nonzero, rdi is now 1 before start of string - bump up to first char
    
;     .done:
;     call r15 ; print the string using the sprinter function in r15

;     pop rsp ; clean up the stack space we allocated for the string
;     ret ; return result from sprinter (number of characters written)

; ------------------------------------------------------------------------------
    
; u64 __printf_u64_decimal(u64 val, __vprintf_fmt_pack *fmt)
; __printf_u64_decimal:
;     mov bl, 0            ; mark that this is not negative
;     mov rcx, 10          ; set to decimal mode (no need to set alpha char in this case)
;     jmp __printf_u64_raw ; then invoke the raw handler
; ; u64 __printf_u32_decimal(u32 val, __vprintf_fmt_pack *fmt)
; __printf_u32_decimal:
;     mov edi, edi             ; zero extend arg to 64-bit
;     jmp __printf_u64_decimal ; then just refer to the 64-bit version
; ; u64 __printf_u16_decimal(u16 val, __vprintf_fmt_pack *fmt)
; __printf_u16_decimal:
;     movzx edi, di            ; zero extend arg to 64-bit
;     jmp __printf_u64_decimal ; then just refer to the 64-bit version
; ; u64 __printf_u8_decimal(u8 val, __vprintf_fmt_pack *fmt)
; __printf_u8_decimal:
;     movzx edi, dil           ; zero extend arg to 64-bit
;     jmp __printf_u64_decimal ; then just refer to the 64-bit version

; ------------------------------------------------------------------------------

; u64 __printf_i64_decimal(i64 val, __vprintf_fmt_pack *fmt)
; __printf_i64_decimal:
;     mov rax, rdi
;     neg rax              ; pre-compute the negative of val in rax
;     cmp rdi, 0
;     setl bl              ; set negative flag in bl
;     movl rdi, rax        ; conditionally copy the negative value (now positive) back into rdi
;     mov rcx, 10          ; set to decimal mode (no need to set alpha char in this case)
;     jmp __printf_u64_raw ; then invoke the raw handler
; ; u64 __printf_i32_decimal(i32 val, __vprintf_fmt_pack *fmt)
; __printf_i32_decimal:
;     movsx rdi, edi           ; sign extend arg to 64-bit
;     jmp __printf_i64_decimal ; then just refer to the 64-bit version
; ; u64 __printf_i16_decimal(i16 val, __vprintf_fmt_pack *fmt)
; __printf_i16_decimal:
;     movsx rdi, di            ; sign extend arg to 64-bit
;     jmp __printf_i64_decimal ; then just refer to the 64-bit version
; ; u64 __printf_i8_decimal(i8 val, __vprintf_fmt_pack *fmt)
; __printf_i8_decimal:
;     movsx rdi, dil           ; sign extend arg to 64-bit
;     jmp __printf_i64_decimal ; then just refer to the 64-bit version

; ------------------------------------------------------------------------------

; u64 __printf_u64_hex(u64 val, __vprintf_fmt_pack *fmt)
; __printf_u64_hex:
;     mov bl, 0            ; mark that this is not negative
;     mov rcx, 16          ; set to hexadecimal mode
;     mov bh, 'a'          ; set lowercase 'a' as base alpha char
;     jmp __printf_u64_raw ; then invoke the raw handler
; ; u64 __printf_u32_hex(u32 val, __vprintf_fmt_pack *fmt)
; __printf_u32_hex:
;     mov edi, edi         ; zero extend arg to 64-bit
;     jmp __printf_u64_hex ; then just refer to the 64-bit version
; ; u64 __printf_u16_hex(u16 val, __vprintf_fmt_pack *fmt)
; __printf_u16_hex:
;     movzx rdi, di        ; zero extend arg to 64-bit
;     jmp __printf_u64_hex ; then just refer to the 64-bit version
; ; u64 __printf_u8_hex(u8 val, __vprintf_fmt_pack *fmt)
; __printf_u8_hex:
;     movzx rdi, dil       ; zero extend arg to 64-bit
;     jmp __printf_u64_hex ; then just refer to the 64-bit version

; ------------------------------------------------------------------------------

; u64 __printf_u64_HEX(u64 val, __vprintf_fmt_pack *fmt)
; __printf_u64_HEX:
;     mov bl, 0            ; mark that this is not negative
;     mov rcx, 16          ; set to hexadecimal mode
;     mov bh, 'A'          ; set uppercase 'A' as base alpha char
;     jmp __printf_u64_raw ; then invoke the raw handler
; ; u64 __printf_u32_HEX(u32 val, __vprintf_fmt_pack *fmt)
; __printf_u32_HEX:
;     mov edi, edi         ; zero extend arg to 64-bit
;     jmp __printf_u64_HEX ; then just refer to the 64-bit version
; ; u64 __printf_u16_HEX(u16 val, __vprintf_fmt_pack *fmt)
; __printf_u16_HEX:
;     movzx rdi, di        ; zero extend arg to 64-bit
;     jmp __printf_u64_HEX ; then just refer to the 64-bit version
; ; u64 __printf_u8_HEX(u8 val, __vprintf_fmt_pack *fmt)
; __printf_u8_HEX:
;     movzx rdi, dil       ; zero extend arg to 64-bit
;     jmp __printf_u64_HEX ; then just refer to the 64-bit version

; ------------------------------------------------------------------------------

; u64 __printf_u64_octal(u64 val, __vprintf_fmt_pack *fmt)
; __printf_u64_octal:
;     mov bl, 0            ; mark that this is not negative
;     mov rcx, 8           ; set to octal mode (no need to set alpha char in this case)
;     jmp __printf_u64_raw ; then invoke the raw handler
; ; u64 __printf_u32_octal(u32 val, __vprintf_fmt_pack *fmt)
; __printf_u32_octal:
;     mov edi, edi           ; zero extend arg to 64-bit
;     jmp __printf_u64_octal ; then just refer to the 64-bit version
; ; u64 __printf_u16_octal(u16 val, __vprintf_fmt_pack *fmt)
; __printf_u16_octal:
;     movzx rdi, di          ; zero extend arg to 64-bit
;     jmp __printf_u64_octal ; then just refer to the 64-bit version
; ; u64 __printf_u8_octal(u8 val, __vprintf_fmt_pack *fmt)
; __printf_u8_octal:
;     movzx rdi, dil         ; zero extend arg to 64-bit
;     jmp __printf_u64_octal ; then just refer to the 64-bit version

; ------------------------------------------------------------------------------

; u64 __printf_floating_fixed_raw(f64 val, __vprintf_fmt_pack *fmt : rsi)
; __printf_floating_fixed_raw:
;     movsd xmm1, xmm0 ; copy value into xmm1 for later
;     movq rax, xmm0
;     and rax, 0x7fffffffffffffff
;     movq xmm0, rax ; and convert the value to positive equivalent

;     mov r10d, dword ptr [rsi + __vprintf_fmt_pack.width]
;     mov r11d, dword ptr [rsi + __vprintf_fmt_pack.prec]
;     add r11d, 400
;     cmp r11d, r10d
;     movg r10d, r11d ; put larger of width / prec+400 in r10d
;     and r10d, ~7 ; round down to a multiple of 8
;     add r10d, 32 ; add some more to still be a multiple of 8 but also have a bit extra
    
;     mov rax, rsp
;     sub rsp, r10 ; allocate that many bytes on the stack
;     push rax     ; save original value of rsp on the stack for restore point later
    
;     mov r11d, r10d
;     sub r11d, dword ptr [rsi + __vprintf_fmt_pack.prec]
;     lea r8, [rsp+8 + r11 - 2] ; r8 points to the decimal point
;     mov r9, r8 ; copy this to r9 for later restore point
    
;     mov byte ptr [r8], '.' ; put the decimal point there
;     inc r8                 ; bump up to start of first digit
    
;     ; reset fpu and set rounding mode to toward 0
;     finit
;     fstcw word ptr [rsp - 2]
;     or word ptr [rsp - 2], 0x0c00
;     fldcw word ptr [rsp - 2]
    
;     mov qword ptr [rsp - 8], 10.0
;     fld qword ptr [rsp - 8]         ; load a 10.0 for multiplication
;     movsd qword ptr [rsp - 8], xmm0
;     fld qword ptr [rsp - 8]         ; load the value

;     fxam     ; examine the value
;     fstsw ax ; store status word to ax
;     sahf     ; update flags
;     jnc .typical
    
;     ; if we get here st0 is either nan, inf, or empty (impossible)
;     movnp r8, $str("nan")
;     movp r8, $str("inf")
;     jmp .print
    
;     .typical:
;     mov ecx, dword ptr [rsi + __vprintf_fmt_pack.prec]
;     jecxz .prec_done
;     .prec_loop:
;         fld1                         ; push a 1 onto the stack
;         fxch                         ; swap so we have value, 1
;         fprem                        ; get remainder of division by 1
;         fstp st1                     ; pop the stack
;         fmul st0, st1                ; multiply st0 [0, 1) by 10
;         fist dword ptr [rsp - 4]     ; store that as an integer on the stack 0..9
;         mov eax, dword ptr [rsp - 4] ; load that into a register
;         add al, '0'                  ; convert to an ascii digit '0'..'9'
        
;         mov byte ptr [r8], al ; store that prec digit to the string
;         inc r8                ; on to next prec digit
        
;         loop .prec_loop
;     .prec_done:
;     mov byte ptr [r8], 0 ; null terminate the string at end of prec digits
    
;     ; get the next digit we would have printed (but don't actually print it)
;     fld1                     ; push a 1 onto the stack
;     fxch                     ; swap so we have value, 1
;     fprem                    ; get remainder of division by 1
;     fstp st1                 ; pop the stack
;     fmul st0, st1            ; multiply st0 [0, 1) by 10
;     fist dword ptr [rsp - 4] ; store that as an integer on the stack 0..9
    
;     cmp dword ptr [rsp - 4], 5 ; compare it to 5
;     setge dl ; if it was >=5 we need to round up by a digit
;              ; we'll do this later (after int part is constructed)
    
;     mov r8, r9 ; load restore point - r8 now points at the decimal point
    
;     fstp st0 ; pop the fpu stack
;     movsd qword ptr [rsp - 8], xmm0
;     fld qword ptr [rsp - 8] ; reload the value
;     frndint                 ; truncate to integer
    
;     .int_loop:
;         fst st2 ; copy value to st2
;         fprem   ; compute remainder of division by 10
;         fistp dword ptr [rsp - 4]    ; store result (truncated) to temp memory and pop
;         mov eax, dword ptr [rsp - 4] ; move that into a register
;         fxch          ; swap st0 and st1 to put the value copy back in st0 and 10.0 back in st1
;         fdiv st0, st1 ; divide value by 10
;         frndint       ; then round back to int
        
;         add al, '0' ; convert digit to ascii
        
;         dec r8 ; make room for new character in string
;         mov byte ptr [r8], al ; store the digit in string
        
;         ftst          ; compare new remainder to zero
;         fstsw ax      ; store fpu flags in ax
;         sahf          ; apply them to eflags
;         jnz .int_loop ; if nonzero, repeat
    
;     cmp dl, 0      ; test the rounding flag (stored in dl)
;     jz .round_done ; if not set, we're done rounding
    
;     lea r9, [rsp+8 + r10 - 2]  ; load address of last significant digit into r9
;     .round_loop:
;         mov al, byte ptr [r9]  ; load this character from the string
;         cmp al, '.'
;         je .round_continue     ; if it's the period, just skip it
;         cmp byte ptr [r9], '9'
;         jne .round_term        ; otherwise if it's not a 9 we're done
;         mov byte ptr [r9], '0' ; otherwise set the digit to 0
        
;         .round_continue:
;         cmp r9, r8
;         je .round_extend ; if we just processed the first char in string and not done, we need to extend string
;         dec r9
;         jmp .round_loop ; otherwise we're not done and need to continue
        
;         .round_term:
;         inc byte ptr [r9] ; increment this character by 1
;         jmp .round_done   ; and now we're done
        
;         .round_extend:
;         dec r8                 ; decrement the string starting pos
;         mov byte ptr [r8], '1' ; append a 1 to the front of the string to finish the rounding
;     .round_done:
    
;     movq rax, xmm1 ; load the original value into rax
;     test rax, 0x8000000000000000
;     jz .print ; if it was positive, we're done
    
;     dec r8                 ; make space for the sign character
;     mov byte ptr [r8], '-' ; append a minus sign to the front of the string
    
;     .print:
;     mov rdi, r8 ; point rdi at the start of the string in the buffer
;     call r15    ; call the sprinter function in r15
    
;     pop rsp ; clean up the stack space we allocated for the string
;     ret ; return result from sprinter (number of characters written)

; ------------------------------------------------------------------------------
    
; u64 __printf_f64_fixed(f64 val, __vprintf_fmt_pack *fmt : rsi)
; __printf_f64_fixed:
;     ; if no precision was specified, set it to a default
;     test dword ptr [rsi + __vprintf_fmt_pack.fmt], __vprintf_fmt.prec
;     movz dword ptr [rsi + __vprintf_fmt_pack.prec], 6
;     jmp __printf_floating_fixed_raw ; jump to the handler
    
; ------------------------------------------------------------------------------

; int __vprintf(const char *fmt, arglist *args, sprinter : r15, sprinter_arg : r14)
; this serves as the implementation for all the various printf functions.
; the format string and arglist should be passed as normal args.
; the arglist should already be advanced to the location of the first arg to print.
; the sprinter function and sprinter arg should be set up in registers r14 and r15
; __vprintf:
;     .BUF_CAP: equ 63 ; amount of buffer space to put on the stack for efficiency
;     .FMT_START: equ 32 ; starting position of fmt pack (has space before it for storing registers)
;     .BUF_START: equ .FMT_START + __vprintf_fmt_pack.SIZE ; starting position of stack buffer (has space before it for fmt pack)
;     .TMP_SIZE: equ 16 ; size of temp space for storing intermediate values on the stack
;     .TMP_START: equ .BUF_START + (.BUF_CAP+1) ; starting position of temp space
;     sub rsp, .BUF_START + (.BUF_CAP+1) + .TMP_SIZE ; put args and call safe registers on the stack + buffer space
;     mov qword ptr [rsp + 0], rdi
;     mov qword ptr [rsp + 8], rsi
;     mov qword ptr [rsp + 16], r12 ; save call-safe register
;     mov qword ptr [rsp + 24], r13 ; save call-safe register
    
;     ; put buffer size in rdi - this is meant to speed up writing to the buffer.
;     ; before a function call, buffer must be flushed, and afterwards this must be reset.
;     xor rdi, rdi ; rdi holds buffer size
    
;     mov r12, qword ptr [rsp + 0] ; r12 holds address of the character we're processing
;     xor r13, r13 ; r13 holds the total number of characters written
;     jmp .loop_tst
;     .loop_bod:
;         cmp al, '%'
;         jne .simple_char ; if it's not a %, just print a simple character
;         inc r12 ; skip to next char (format flag)
;         mov al, byte ptr [r12] ; get the following character
;         cmp al, 0
;         jz .invalid ; if it's a terminator, invalid format string
        
;         cmp al, '%'
;         je .simple_char ; escape % can just be printed by simple char code
        
;         ; parse the format prefix
;         lea rsi, [rsp + .FMT_START]
;         mov r10, qword ptr [rsp + 8]
;         call __vprintf_read_prefix
;         cmp eax, 0
;         jnz .invalid ; if that returned nonzero we failed to parse prefix
        
;         mov al, byte ptr [r12] ; we need to reload the format character after parsing prefix (pos moved)
        
;         cmp al, 'd'
;         je .d_formatter
;         cmp al, 'i'
;         je .i_formatter
;         cmp al, 'u'
;         je .u_formatter
;         cmp al, 'x'
;         je .x_formatter
;         cmp al, 'X'
;         je .X_formatter
;         cmp al, 'o'
;         je .o_formatter
;         cmp al, 's'
;         je .string
;         cmp al, 'c'
;         je .char
;         cmp al, 'f'
;         je .f_formatter
        
;         ; otherwise unknown flag
;         .invalid:
;         push rdi
;         mov rdi, $str(`\n[[ERROR]] unrecognized printf format character\n`)
;         mov rsi, stderr
;         call fputs
;         pop rdi
;         jmp .loop_brk
;         ; prints a message denoting that the specified size was invalid for this option
;         .invalid_size:
;         mov rdi, $str(`\n[[ERROR]] unrecognized printf size prefix\n`)
;         mov rsi, stderr
;         call fputs
;         pop rdi
;         jmp .loop_brk
        
;         .o_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_ofetch ; load the ofetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_oprint ; load the oprint array into temp[1]
;         jmp .generic_formatter
        
;         .X_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_Xfetch ; load the Xfetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_Xprint ; load the Xprint array into temp[1]
;         jmp .generic_formatter
        
;         .x_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_xfetch ; load the xfetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_xprint ; load the xprint array into temp[1]
;         jmp .generic_formatter
        
;         .u_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_ufetch ; load the ufetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_uprint ; load the uprint array into temp[1]
;         jmp .generic_formatter
        
;         .i_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_ifetch ; load the ifetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_iprint ; load the iprint array into temp[1]
;         jmp .generic_formatter
        
;         .d_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_dfetch ; load the dfetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_dprint ; load the dprint array into temp[1]
;         jmp .generic_formatter
        
;         .f_formatter:
;         mov qword ptr [rsp + .TMP_START + 0], __printf_fmt_ffetch ; load the dfetch array into temp[0]
;         mov qword ptr [rsp + .TMP_START + 8], __printf_fmt_fprint ; load the dprint array into temp[1]
        
;         ; requires a fetch array in temp[0] and a print array in temp[1] (see above) - fetch null iff print null
;         ; invokes generic formatting logic on the next parameter in the arglist
;         .generic_formatter:
;         call .__FLUSH_BUFFER                                             ; flush the buffer before we do the formatted output
;         mov rdi, qword ptr [rsp + 8]                                     ; load the arglist
;         mov r8d, dword ptr [rsp + .FMT_START + __vprintf_fmt_pack.scale] ; load the scale value from format pack
;         mov rbx, qword ptr [rsp + .TMP_START + 0]                        ; get the fetcher array from temp[0]
;         mov rax, qword ptr [rbx + r8*8]                                  ; get the arg fetcher for this size
;         cmp rax, 0                                                       ; check if the arg fetcher is valid
;         jz .invalid_size                                                 ; if the arg fetcher was invlaid, print error message
;         call rax                                                         ; otherwise invoke the arg fetcher (result in rax)
;         mov rdi, rax                                                     ; copy the result of arg fetcher into rdi
;         lea rsi, [rsp + .FMT_START]                                      ; load the address of the format packet into rsi
;         mov rbx, qword ptr [rsp + .TMP_START + 8]                        ; get the printer array from temp[1]
;         call qword ptr [rbx + r8*8]                                      ; then call the printer for this size (assumed to be valid because fetcher was valid)
;         add r13, rax                                                     ; update total printed chars
;         xor rdi, rdi                                                     ; reset the buffer after formatted output 
;         jmp .loop_aft
        
;         .string:
;         call .__FLUSH_BUFFER         ; flush the buffer before we do the formatted output
;         mov rdi, qword ptr [rsp + 8] ; load the arglist
;         call arglist_i               ; get the pointer (64-bit integer)
;         mov rdi, rax                 ; put it in rdi
;         call r15                     ; print the string using the sprinter function
;         add r13, rax                 ; update total printed chars
;         xor rdi, rdi                 ; reset the buffer after formatted output
;         jmp .loop_aft
        
;         .char:
;         mov qword ptr [rsp + .TMP_START], rdi ; save buffer size in tmp space
;         mov rdi, qword ptr [rsp + 8]          ; load the arglist
;         call arglist_i                        ; get the character to print (8-bit integer) (now in al)
;         mov rdi, qword ptr [rsp + .TMP_START] ; reload the buffer size
        
;         ; FALL THROUGH INTENTIONAL
        
;         .simple_char:
;         cmp rdi, .BUF_CAP
;         jb .simple_char_append ; if the buffer has space, just append
;         mov byte ptr [rsp + .TMP_START], al ; otherwise store the character in tmp space (in case we clobber it)
;         call .__FLUSH_BUFFER                ; then flush the (full) buffer
;         xor rdi, rdi                        ; and reset it
;         mov al, byte ptr [rsp + .TMP_START] ; reload the character to append from tmp space
;         .simple_char_append:
;         mov byte ptr [rsp + .BUF_START + rdi], al ; append the character to the buffer
;         inc rdi ; and bump up buffer size
;     .loop_aft:
;         inc r12
;     .loop_tst:
;         mov al, byte ptr [r12]
;         cmp al, 0
;         jnz .loop_bod
;     .loop_brk:

;     ; perform one final buffer flush in case we had anything left in it
;     call .__FLUSH_BUFFER

;     add rsp, .BUF_START + (.BUF_CAP+1) + .TMP_SIZE ; clean up stack space
    
;     mov rax, r13 ; return total number of characters written
;     ret
; this is a pseudo-function to call which flushes buffer.
; the buffer must be reinitialized after this operation (e.g. after any functions calls).
; .__FLUSH_BUFFER:
;     cmp rdi, 0
;     jz .__FLUSH_BUFFER_noop ; if the buffer is empty we don't need to do the overhead of printing it
    
;     ; terminate the buffer (C string)
;     mov byte ptr [rsp + 8 + .BUF_START + rdi], 0 ; +8 skips the return address
;     ; call the sprinter function
;     lea rdi, [rsp + 8 + .BUF_START]
;     call r15
;     ; add #characters written to total char count
;     add r13, rax
    
;     .__FLUSH_BUFFER_noop:
;     ret

; --------------------------------------

; int vsnprintf(char *s, u64 n, const char *fmt, arglist *args)
; vsnprintf:
;     cmp rsi, 0
;     jz .noop ; if n == 0 do nothing - don't even trivially null terminate the buffer
    
;     push r14
;     push r15
    
;     mov byte ptr [rdi], 0 ; null terminate buffer in case result is empty string (never calls sprinter)
    
;     ; create the sprinter arg structure
;     dec rsi  ; n is size of array, so n-1 is max number of chars to write (+ the null terminator)
;     push rsi ; arg[1] holds the maximum number of characters we can still write to the buffer
;     push rdi ; arg[0] holds the address at which to perform string cat
    
;     mov r14, rsp
;     mov rdi, rdx
;     mov rsi, rcx
;     mov r15, .__SPRINTER
;     call __vprintf
    
;     add rsp, 16 ; destroy the sprinter arg structure when we're done
    
;     pop r15
;     pop r14
;     ret
    
;     .noop:
;     xor eax, eax
;     ret
    
;     .__SPRINTER:
;         mov rbx, rdi
;         mov rcx, -1
;         mov al, 0
;         cld
;         repne scasb ; rdi is now 1 past first null terminator
        
;         dec rdi
;         sub rdi, rbx                 ; compute length of string to append
;         mov rdx, qword ptr [r14 + 8] ; fetch number of chars we can actually append
;         cmp rdx, rdi                 ; compare them
;         movb rdi, rdx                ; if num we can actually append is smaller, use it instead
        
;         mov rcx, rdi ; put length of string into count
;         mov rax, rdi ; also store in return value for later
        
;         mov rsi, rbx
;         mov rdi, qword ptr [r14] ; buffer is dest (we point at its null terminator)
;         rep movsb                ; append the string to the end of the buffer (as many chars as we can, perhaps none)
;         mov byte ptr [rdi], 0    ; null terminate the result
;         mov qword ptr [r14], rdi ; update the sprinter pos parameter
        
;         sub qword ptr [r14 + 8], rax ; update the sprinter max num additional chars parameter
        
;         ret ; return number of chars printed (excluding null terminator)
; ; int snprintf(char *s, u64 n, const char *fmt, ...)
; snprintf:
;     mov r10, rsp
;     push r15
;     call arglist_start
;     push rax
;     push rdx
;     push rsi
;     push rdi
;     mov rdi, rax
;     times 3 call arglist_i

;     mov rcx, rdi
;     pop rdi
;     pop rsi
;     pop rdx
;     call vsnprintf
;     mov r15, rax
    
;     pop rdi
;     call arglist_end
;     mov rax, r15
;     pop r15
;     ret
        
; ; int vsprintf(char *s, const char *fmt, arglist *args)
; vsprintf:
;     push r14
;     push r15
    
;     mov byte ptr [rdi], 0 ; null terminate buffer in case result is empty string (never calls sprinter)
    
;     mov r14, rdi
;     mov rdi, rsi
;     mov rsi, rdx
;     mov r15, .__SPRINTER
;     call __vprintf
    
;     pop r15
;     pop r14
;     ret
    
;     .__SPRINTER:
;         mov rbx, rdi
;         mov rcx, -1
;         mov al, 0
;         cld
;         repne scasb ; rdi is now 1 past first null terminator
        
;         dec rdi
;         sub rdi, rbx ; compute length of string to append
        
;         mov rcx, rdi ; put length of string into count
;         mov rax, rdi ; also store in return value for later
        
;         mov rsi, rbx
;         mov rdi, r14          ; buffer is dest (we point at its null terminator)
;         rep movsb             ; append the string to the end of the buffer
;         mov byte ptr [rdi], 0 ; null terminate the result
;         mov r14, rdi          ; update the sprinter pos parameter
        
;         ret ; return number of chars printed (excluding null terminator)
; ; int sprintf(char *s, const char *fmt, ...)
; sprintf:
;     mov r10, rsp
;     push r15
;     call arglist_start
;     push rax
;     push rsi
;     push rdi
;     mov rdi, rax
;     times 2 call arglist_i

;     mov rdx, rdi
;     pop rdi
;     pop rsi
;     call vsprintf
;     mov r15, rax
    
;     pop rdi
;     call arglist_end
;     mov rax, r15
;     pop r15
;     ret
        
; ; int vfprintf(FILE *stream, const char *fmt, arglist *args)
; vfprintf:
;     push r14
;     push r15
    
;     mov r14, rdi
;     mov rdi, rsi
;     mov rsi, rdx
;     mov r15, .__SPRINTER
;     call __vprintf
    
;     pop r15
;     pop r14
;     ret
    
;     .__SPRINTER:
;         mov rsi, r14
;         jmp fputs
; ; int fprintf(FILE *stream, const char *fmt, ...)
; fprintf:
;     mov r10, rsp
;     push r15
;     call arglist_start
;     push rax
;     push rsi
;     push rdi
;     mov rdi, rax
;     times 2 call arglist_i

;     mov rdx, rdi
;     pop rdi
;     pop rsi
;     call vfprintf
;     mov r15, rax
    
;     pop rdi
;     call arglist_end
;     mov rax, r15
;     pop r15
;     ret

; ; int vprintf(const char *fmt, arglist *args)
; vprintf:
;     mov rdx, rsi
;     mov rsi, rdi
;     mov rdi, stdout
;     jmp vfprintf
; ; int printf(const char *fmt, ...)
; printf:
;     mov r10, rsp
;     push r15
;     call arglist_start
;     push rax
;     push rdi
;     mov rdi, rax
;     call arglist_i
    
;     mov rsi, rdi
;     pop rdi
;     call vprintf
;     mov r15, rax
    
;     pop rdi
;     call arglist_end
;     mov rax, r15
;     pop r15
;     ret
    
; --------------------------------------

; int ungetc(int character, FILE *stream)
; ungetc:
;     mov dword ptr [rsi + FILE.ungetc_ch], edi ; discard old ungetc_ch if present
;     mov eax, edi ; return the character
;     ret

; ; int getchar(void)
; getchar:
;     mov rdi, stdin
; ; int fgetc(FILE *stream)
; fgetc:
;     mov eax, dword ptr [rdi + FILE.ungetc_ch]
;     cmp eax, EOF
;     jne .fetch_ungetc_ch ; if there's an unget char, get that

;     ; otherwise read a character from the stream (native buffers for us)
;     mov eax, sys_read
;     mov ebx, dword ptr [rdi + FILE.fd]
;     lea rcx, byte ptr [rsp - 1] ; place the read character on the stack (red zone)
;     mov edx, 1
;     syscall
    
;     ; if that failed, return EOF
;     cmp rax, 0
;     jle .fail
;     ; otherwise return the read character
;     movzx eax, byte ptr [rsp - 1]
;     ret
    
;     .fail:
;     mov eax, EOF
;     ret
    
;     .fetch_ungetc_ch:
;     mov dword ptr [rdi + FILE.ungetc_ch], EOF ; mark ungetc char as eof (none)
;     ret ; and return the old ungetc char value

; ; int fpeek(FILE *stream) -- nonstandard convenience function
; fpeek:
;     call fgetc
;     mov rsi, rdi
;     mov edi, eax
;     jmp ungetc

; --------------------------------------

; FILE *fopen(const char *filename, const char *mode)
; fopen:
;     mov al, 0 ; + flag
;     mov bl, 0 ; b flag

;     mov r8, rsi
;     jmp .loop_tst
;     .loop_top:
;         cmp dl, '+'
;         move al, 1
;         cmp dl, 'b'
;         move bl, 1
;     .loop_aft:
;         inc r8
;     .loop_tst:
;         mov dl, byte ptr [r8]
;         cmp dl, 0
;         jne .loop_top
    
;     xor r8, r8 ; flags
    
;     mov dl, byte ptr [rsi]
;     cmp dl, 'r' ; if reading
;     je .reading
;     cmp dl, 'w' ; if writing
;     je .writing
;     cmp dl, 'a' ; if appending
;     je .appending
;     xor rax, rax ; otherwise invalid mode
;     ret

;     .reading:
;     cmp al, 0
;     movz  r8, O_RDONLY
;     movnz r8, O_RDWR
;     jmp .finish
    
;     .writing:
;     cmp al, 0
;     movz  r8, O_CREAT | O_WRONLY | O_TRUNC
;     movnz r8, O_CREAT | O_RDWR   | O_TRUNC
;     jmp .finish
    
;     .appending:
;     cmp al, 0
;     movz  r8, O_CREAT | O_WRONLY | O_APPEND
;     movnz r8, O_CREAT | O_RDWR   | O_APPEND
    
;     .finish:
;     ; call native open
;     mov eax, sys_open
;     mov rbx, rdi
;     mov rcx, r8
;     syscall
;     ; if it fails, return null
;     cmp eax, -1
;     jne .success
;     xor rax, rax
;     ret
;     .success:
    
;     push eax ; save the fd
    
;     ; allocate the FILE object
;     mov rdi, FILE.SIZE
;     call malloc
;     ; if it fails, return null
;     cmp rax, 0
;     jne .success_2
;     xor rax, rax
;     ret
;     .success_2:
    
;     ; initialize the FILE object
;     pop dword ptr [rax + FILE.fd] ; restore the fd
;     mov dword ptr [rax + FILE.ungetc_ch], EOF ; set no ungetc char
;     mov dword ptr [rax + FILE.static], 0 ; set as not static (will pass to free())
    
;     ; return address of the FILE object
;     ret
    
; ; int fclose(FILE *stream)
; fclose:
;     call fflush ; flush the stream
    
;     ; invoke native close
;     mov eax, sys_close
;     mov ebx, dword ptr [rdi + FILE.fd]
;     syscall
;     push eax ; save native close result
    
;     ; if non-static, free the FILE object
;     cmp dword ptr [rdi + FILE.static], 0
;     jnz .done
;     call free ; free the FILE object
;     .done:
    
;     pop eax ; return native close result
;     ret

; ; int fflush(FILE *stream)
; fflush:
;     xor eax, eax ; CSX64 does this for us, so no need to buffer
;     ret
    
; --------------------------------------

; segment rodata

; align 8
; __printf_fmt_dfetch: ; arg fetchers for %d option
; __printf_fmt_ifetch: ; %i will use the same arg fetchers
; __printf_fmt_ufetch: ; %u will use the same arg fetchers
; __printf_fmt_xfetch: ; %x will use the same arg fetchers
; __printf_fmt_Xfetch: ; %X will use the same arg fetchers
; __printf_fmt_ofetch: ; %o will use the same arg fetchers
;     dq arglist_i ; default
;     dq arglist_i ; hh
;     dq arglist_i ; h
;     dq arglist_i ; l
;     dq arglist_i ; ll
;     dq arglist_i ; j
;     dq arglist_i ; z
;     dq arglist_i ; t
;     dq 0         ; L
; static_assert $-__printf_fmt_dfetch == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_ffetch: ; arg fetchers for %f option
;     dq arglist_f ; default
;     dq 0         ; hh
;     dq 0         ; h
;     dq arglist_f ; l
;     dq 0         ; ll
;     dq 0         ; j
;     dq 0         ; z
;     dq 0         ; t
;     dq 0         ; L
; static_assert $-__printf_fmt_ffetch == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_dprint: ; printer functions for the %d option
; __printf_fmt_iprint: ; %i will use the same printers
;     dq __printf_i32_decimal ; default
;     dq __printf_i8_decimal  ; hh
;     dq __printf_i16_decimal ; h
;     dq __printf_i64_decimal ; l
;     dq __printf_i64_decimal ; ll
;     dq __printf_i64_decimal ; j
;     dq __printf_i64_decimal ; z
;     dq __printf_i64_decimal ; t
;     dq 0                    ; L
; static_assert $-__printf_fmt_dprint == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_uprint:
;     dq __printf_u32_decimal ; default
;     dq __printf_u8_decimal  ; hh
;     dq __printf_u16_decimal ; h
;     dq __printf_u64_decimal ; l
;     dq __printf_u64_decimal ; ll
;     dq __printf_u64_decimal ; j
;     dq __printf_u64_decimal ; z
;     dq __printf_u64_decimal ; t
;     dq 0                    ; L
; static_assert $-__printf_fmt_uprint == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_xprint:
;     dq __printf_u32_hex ; default
;     dq __printf_u8_hex  ; hh
;     dq __printf_u16_hex ; h
;     dq __printf_u64_hex ; l
;     dq __printf_u64_hex ; ll
;     dq __printf_u64_hex ; j
;     dq __printf_u64_hex ; z
;     dq __printf_u64_hex ; t
;     dq 0                ; L
; static_assert $-__printf_fmt_xprint == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_Xprint:
;     dq __printf_u32_HEX ; default
;     dq __printf_u8_HEX  ; hh
;     dq __printf_u16_HEX ; h
;     dq __printf_u64_HEX ; l
;     dq __printf_u64_HEX ; ll
;     dq __printf_u64_HEX ; j
;     dq __printf_u64_HEX ; z
;     dq __printf_u64_HEX ; t
;     dq 0                ; L
; static_assert $-__printf_fmt_Xprint == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_oprint:
;     dq __printf_u32_octal ; default
;     dq __printf_u8_octal  ; hh
;     dq __printf_u16_octal ; h
;     dq __printf_u64_octal ; l
;     dq __printf_u64_octal ; ll
;     dq __printf_u64_octal ; j
;     dq __printf_u64_octal ; z
;     dq __printf_u64_octal ; t
;     dq 0                  ; L
; static_assert $-__printf_fmt_oprint == __vprintf_scale.COUNT * 8

; align 8
; __printf_fmt_fprint:
;     dq __printf_f64_fixed ; default
;     dq 0                  ; hh
;     dq 0                  ; h
;     dq __printf_f64_fixed ; l
;     dq 0                  ; ll
;     dq 0                  ; j
;     dq 0                  ; z
;     dq 0                  ; t
;     dq 0                  ; L
; static_assert $-__printf_fmt_fprint == __vprintf_scale.COUNT * 8

segment data

align FILE.ALIGN
stdin:
    dd 0   ; fd
    dd EOF ; ungetc_ch
    dd 1   ; static
static_assert $-stdin == FILE.SIZE

align FILE.ALIGN
stdout:
    dd 1   ; fd
    dd EOF ; ungetc_ch
    dd 1   ; static
static_assert $-stdout == FILE.SIZE

align FILE.ALIGN
stderr:
    dd 2   ; fd
    dd EOF ; ungetc_ch
    dd 1   ; static
static_assert $-stderr == FILE.SIZE
