; source http://www.cplusplus.com/reference/cstdlib/

global malloc
global free
; global calloc
; global realloc

; these are global but you should never modify them.
; should only by touched once by start.asm for initialization.
global __malloc_beg, __malloc_end

segment text

; void *_align(void *ptr, u64 align);
; align value must be a power of 2
_align:
    ; make a copy of ptr in the return value
    mov rax, rdi

    ; compute the required alignment offset
    neg rdi
    dec rsi
    and rdi, rsi

    ; apply the offset and return the aligned pointer
    add rax, rdi
    ret

; the amount of memory for malloc to request at a time (must be a power of 2)
_malloc_step: equ 1 * 1024 * 1024 ; 1 MB

; custom (naive) malloc impl structure:
;            V initial sys brk (base of stack space)
; <--- stack | ([void *next][void *prev][... data ...])...
;              ^ doubly-linked list of zero or more malloc data blocks
; 
; we shall assume no one else will be manipulating memory beyond the initial breakpoint
; pointers will be 8-byte aligned.
; bit 0 of next will hold 1 if this block is occupied.
; 
; void *malloc(u64 size);
; allocates contiguous memory in dynamically-allocated space via sys_brk.
; you should not directly call sys_brk at any time (except in the case where it just returns the current break).
; the memory returned is aligned on 8-byte boundaries.
; the pointer returned by this function must later be dealocated by calling free().
; allocating 0 bytes returns null.
; upon failure (e.g. sys_brk refused), returns null.
; upon success, returns a pointer to the allocated memory.
; dereferencing this pointer out of bounds is undefined behavior.
malloc:
    ; allocating 0 returns null
    cmp rdi, 0
    jnz .beg
    xor rax, rax
    ret
    
    .beg:
    ; align request size to 8-byte blocks
    mov esi, 8
    call _align
    mov rdi, rax
    
    ; get the beg/end positions
    mov rsi, [__malloc_beg]
    mov r8,  [__malloc_end]
    ; if beg was nonzero, we're good
    cmp rsi, 0
    jnz .ok
    
    ; otherwise initialize beg/end and reload
    ; this just sets beg/end - doesn't allocate any space
    mov r11, rdi
    mov eax, sys_brk
    xor ebx, ebx
    syscall
    mov rdi, rax
    mov esi, 8
    call _align
    mov [__malloc_beg], rax
    mov [__malloc_end], rax
    mov rsi, rax
    mov r8, rax
    mov rdi, r11

    .ok:
    ; look through the list for an available block of sufficient size
    ; for(void *prev = 0, *pos = beg; pos < end; prev = pos, pos = pos->next)
    ; -- prev = r12
    ; -- pos = rsi
    ; -- end = r8
    xor r12, r12
    jmp .aft
    .top:
        ; get the next pointer
        mov rdx, [rsi]
        btr rdx, 0
        
        ; if it's occupied, skip
        jc .cont
        
        ; compute size - if it's not big enough, it won't work
        mov rcx, rdx
        sub rcx, rsi
        sub rcx, 16
        cmp rcx, rdi
        jb .cont
        
        ; -- yay we got one -- ;
        
        ; split the block if it's large enough (that the split block's size > 0)
        ; if (block_size >= request + 24)
        mov rax, rdi
        add rax, 24
        cmp rcx, rax
        jb .nosplit
        
        ; splitting block - get pointer to start of split
        lea rbx, [rsi + 16 + rdi]
        
        ; update split's next/prev (unoccupied)
        mov [rbx], rdx
        mov [rbx + 8], rsi
        
        ; if next is in bounds, update next->prev
        cmp rdx, r8
        movb [rdx + 8], rbx
        
        ; update register that holds our next
        mov rdx, rbx
        
        .nosplit:
        or dl, 1 ; mark this block as occupied
        mov [rsi], rdx
        lea rax, [rsi + 16] ; return pointer to data array
        ret
        
    .cont:
        mov r12, rsi
        mov rsi, rdx
    .aft:
        cmp rsi, r8
        jb .top
    
    ; -- if we got here, we went out of range of the malloc field -- ;
    
    ; put position to add block in r8 (overwrite prev if not in use, otherwise __malloc_end)
    cmp r12, 0
    jz .begin_add
    mov rax, [r12]
    bt rax, 0
    movnc r8, r12
    movnc r12, [r8 + 8]
    
    .begin_add:
    ; get program break
    mov eax, sys_brk
    xor ebx, ebx
    syscall
    
    ; if we have room, create a new block on the end and take that
    lea r10, [r8 + 16 + rdi]
    cmp r10, rax
    ja .nospace
    
    .enough_space:
    ; we have enough space - create the new block on the end (occupied)
    mov [__malloc_end], r10
    or r10b, 1
    mov [r8], r10
    mov [r8 + 8], r12
    lea rax, [r8 + 16]
    ret
    
    .nospace:
    ; otherwise we have no space - get amount of space to allocate (multiple of step)
    mov r11, rdi
    mov rdi, r10
    sub rdi, rax
    mov rsi, _malloc_step
    call _align
    mov rdi, r11

    ; add that much memory
    mov r9, rax
    mov eax, sys_brk
    xor ebx, ebx
    syscall
    lea rbx, [rax + r9]
    mov eax, sys_brk
    syscall

    ; if we got a zero return, we're good
    cmp rax, 0
    jz .enough_space
    ; otherwise it failed - return null
    xor rax, rax
    ret
; void *calloc(qword size);
; as malloc except that it also zeroes the contents.
; calloc:
;     ; align the size (for later)
;     mov esi, 8
;     call _align
;     push rax
    
;     ; allocate the memory
;     mov rdi, rax
;     call malloc ; array in rax
;     pop rcx     ; size in rcx
    
;     ; if it returned null, early exit
;     cmp rax, 0
;     jz .ret
    
;     ; zero the contents
;     mov r8,  rax ; save return value in r8
;     mov rdi, rax ; set fill destination
;     xor rax, rax ; set fill value
;     shr rcx, 3   ; get # of 64-bit blocks to fill
; 	cld          ; set forward fill mode
;     rep stosq    ; fill with zero
;     mov rax, r8  ; restore return value
    
;     .ret: ret
; void *realloc(void *ptr, qword size);
; creates a new aray with the specified size and copies over the contents.
; the resulting array is identical up to the lesser of the two sizes.
; if posible, the resize is performed in-place.
; returns a pointer to the new array.
; reallocating a null pointer is equivalent to calling malloc()
; reallocating to a size of zero is equivalent to calling free() (and returns null).
; realloc:
;     ; if pointer is null, call malloc()
;     cmp rdi, 0
;     jnz .non_null
;     mov rdi, rsi
;     call malloc
;     ret
;     .non_null:
    
;     ; if size is zero, call free()
;     cmp rsi, 0
;     jnz .resize
;     call free
;     xor rax, rax
;     ret
;     .resize:
    
;     ; align the size (for later)
;     mov r8, rdi
;     mov rdi, rsi
;     mov esi, 8
;     call _align
;     mov rsi, rax ; aligned size back in rsi
;     mov rdi, r8  ; pointer back in rdi
    
;     ; compute the size of this block
;     mov rcx, [rdi - 16]
;     and cl, ~1
;     mov rbx, rcx ; save a copy of next in rbx
;     sub rcx, rdi
    
;     ; if we already have enough space, we're good
;     cmp rcx, rsi
;     jae .ret
;     ; compute the smaller size into rcx
;     mova rcx, rsi
    
;     ; we're going down the route of needing a new array
;     ; if next is __malloc_end, we can still do it in-place
;     cmp rbx, [__malloc_end]
;     jne .new_array
    
;     mov eax, sys_brk
;     xor ebx, ebx
;     syscall             ; current break point in rax
;     lea r8, [rdi + rsi] ; break point needed in r8 (this is why we aligned size earlier)
    
;     ; if we have enough room, just move __malloc_end
;     cmp r8, rax
;     ja .more_mem
    
;     .good_mem:
;     mov [__malloc_end], r8
;     or r8b, 1
;     mov [rdi - 16], r8
;     mov rax, rdi
;     ret
    
;     .more_mem:
;     ; otherwise we need to allocate more space
;     ; align request size to a multiple of _malloc_step
;     mov r10, rdi
;     mov r11, rax ; save current break in r11
;     mov rdi, r8
;     sub rdi, rax
;     mov rsi, _malloc_step
;     call _align
;     ; and allocate that much extra memory
;     mov rbx, rax
;     add rbx, r11
;     mov eax, sys_brk
;     syscall
;     mov rdi, r10
    
;     ; if it succeeded, we're done
;     cmp rax, 0
;     jz .good_mem
;     ; otherwise it failed - return null
;     xor rax, rax
;     ret
    
;     .new_array: ; sad days, everybody, we need a new array
    
;     ; otherwise we need a new array
;     push rcx
;     push rdi
;     mov rdi, rsi
;     call malloc
;     mov rsi, rax ; new array in rsi
;     pop rdi      ; old array in rdi
;     pop rcx      ; smaller size in rcx
    
;     ; copy the contents up to the smaller size
;     ; (this is why we aligned the size earlier)
;     jrcxz .done ; hopefully refundant but safer to check
;     .loop:
;         sub rcx, 8
;         mov rax, [rdi + rcx]
;         mov [rsi + rcx], rax
;         jnz .loop
    
;     .done:
;     ; free the old array
;     push rsi
;     call free
;     pop rax
;     ret
    
;     .ret:
;     mov rax, rdi
;     ret
; void free(void *ptr);
; deallocated resources that were allocated by malloc.
; the specified pointer must be exactly what was returned by malloc.
; freeing the same pointer twice is undefined behavior
free:
    ; get the raw pointer
    sub rdi, 16
    
    ; get next in rdx
    mov rdx, [rdi]
    and dl, ~1
    ; if next is in range and not in use, get next->next in rdx (we'll merge right)
    cmp rdx, [__malloc_end]
    jae .nomerge_right
    mov rcx, [rdx]
    bt rcx, 0
    movnc rdx, rcx
    .nomerge_right:
    
    ; get prev in rcx
    mov rcx, [rdi + 8]
    ; if prev is in range and not in use, merge with it
    cmp rcx, 0
    jz .nomerge_left
    mov rbx, [rcx]
    bt rbx, 0
    jc .nomerge_left
    mov [rcx], rdx ; this merges left and right simultaneously
    ret
    
    .nomerge_left:
    ; if we're not merging left, we still need to merge right (even if just to mark as not in use)
    mov [rdi], rdx
    ret

segment bss

align 8
__malloc_beg: resq 1 ; starting address for malloc
__malloc_end: resq 1 ; stopping address for malloc
