extern start

extern __malloc_beg, __malloc_end, __malloc_align
extern exit

segment text
    
    ; initialize malloc beg/end pointers - rbp currently holds a pointer to end of memory
    ; make sure to satisfy malloc's data structure alignment requirements
    mov rax, rbp
    neg rax
    and rax, __malloc_align - 1
    add rax, rbp
    mov qword ptr [__malloc_beg], rax
    mov qword ptr [__malloc_end], rax
    
    call start
    mov rdi, rax
    call exit