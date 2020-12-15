extern start

; extern __malloc_beg, __malloc_end

segment text
    
	; initialize malloc beg/end pointers.
	; rbp currently holds a pointer to just past the stack.
	; mov qword ptr [__malloc_beg], rbp
	; mov qword ptr [__malloc_end], rbp
	
    call start
    mov ebx, eax
    mov eax, sys_exit
    syscall
