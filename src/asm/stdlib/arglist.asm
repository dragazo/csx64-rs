global arglist_start, arglist_end

; contract: these functions may only modify rax/xmm0
global arglist_i, arglist_f

segment text

arglist: equ 0
	.SIZE:  equ 136
	
	.int_index:   equ 0 ; u32
	.float_index: equ 4 ; u32
	.stack_pos:   equ 8 ; void*
	
	.root_rsp:  equ 16 ; void*
	
	.int_arr:   equ 24 ; u64[6]
	.float_arr: equ 72 ; f64[8]

; arglist *arglist_start(void *rsp_init : r10)
;
; returns an arglist that iterates over all csxdecl function arguments.
; can be called from any csxdecl function (must be before any arg registers are modified).
; any arguments that were passed in registers are preserved.
; any arguments that were passed on the stack must be accessed relative to rsp_init (see below).
; the returned pointer must be passed to arglist_end() at the end of the function.
; arglist_end() must be called when the stack pointer is in the same position as it was when arglist_start() returned.
;
; rsp_init - the initial value of rsp upon entering the csxdecl function (must be passed in r10).
arglist_start:
	pop rbx      ; pop the return address off the stack
	mov r11, rsp ; put current stack pos in r11 (this is the root rsp value for arglist_end)
	
	add r10, 8 ; put caller's stack arg location in r10 (rsp_init+8 to skip their ret address)
	sub rsp, arglist.SIZE ; allocate stack space for the arglist struct
	
	; initialize the arglist object
	mov dword ptr [rsp + arglist.int_index], 0
	mov dword ptr [rsp + arglist.float_index], 0
	mov qword ptr [rsp + arglist.stack_pos], r10
	mov qword ptr [rsp + arglist.root_rsp], r11

    ; copy all the integral registers
	mov qword ptr [rsp + arglist.int_arr + 0*8], rdi
	mov qword ptr [rsp + arglist.int_arr + 1*8], rsi
	mov qword ptr [rsp + arglist.int_arr + 2*8], rdx
	mov qword ptr [rsp + arglist.int_arr + 3*8], rcx
	mov qword ptr [rsp + arglist.int_arr + 4*8], r8
	mov qword ptr [rsp + arglist.int_arr + 5*8], r9

    ; copy all the floating point registers
    vmovsd qword ptr [rsp + arglist.float_arr + 0*8], xmm0
    vmovsd qword ptr [rsp + arglist.float_arr + 1*8], xmm1
    vmovsd qword ptr [rsp + arglist.float_arr + 2*8], xmm2
    vmovsd qword ptr [rsp + arglist.float_arr + 3*8], xmm3
    vmovsd qword ptr [rsp + arglist.float_arr + 4*8], xmm4
    vmovsd qword ptr [rsp + arglist.float_arr + 5*8], xmm5
    vmovsd qword ptr [rsp + arglist.float_arr + 6*8], xmm6
    vmovsd qword ptr [rsp + arglist.float_arr + 7*8], xmm7
	
	mov rax, rsp ; place arglist pointer in return location
	jmp rbx      ; jump back to the return address we popped off the stack

; void arglist_end(arglist *list)
; this MUST be called with the return value from arglist_start() (see arglist_start()).
; failure to do so may result in memory leaks or random undefined errors.
; this releases any resources used by list and invalidates it.
arglist_end:
	pop rbx ; pop the return address off the stack
	
	mov rsp, qword ptr [rdi + arglist.root_rsp] ; all we need to do is undo our stack allocations by restoring root rsp
	
	jmp rbx ; jump back to the return address we popped of the stack

; ---------------------------------------------

; u64 arglist_i(arglist*)
; gets the next integer argument and stores it in rax.
arglist_i:
	mov eax, dword ptr [rdi + arglist.int_index]
	cmp eax, 6
	jae .get_from_stack
	
	mov rax, qword ptr [rdi + arglist.int_arr + rax*8]
	inc dword ptr [rdi + arglist.int_index]
	ret

	.get_from_stack:
	mov rax, qword ptr [rdi + arglist.stack_pos]
	mov rax, qword ptr [rax]
	add qword ptr [rdi + arglist.stack_pos], 8
	ret

; f64 arglist_i(arglist*)
; gets the next floating point argument and stores it in xmm0.
arglist_f:
	mov eax, dword ptr [rdi + arglist.float_index]
	cmp eax, 8
	jae .get_from_stack
	
	vmovsd xmm0, qword ptr [rdi + arglist.float_arr + rax*8]
	inc dword ptr [rdi + arglist.float_index]
	ret

	.get_from_stack:
	mov rax, qword ptr [rdi + arglist.stack_pos]
	vmovsd xmm0, qword ptr [rax]
	add qword ptr [rdi + arglist.stack_pos], 8
	ret
