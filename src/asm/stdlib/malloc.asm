global malloc, free, realloc, calloc

; these are global but you should never modify them.
; should only by touched once by start.asm for initialization.
global __malloc_beg, __malloc_end, __malloc_align

segment text

; void *_align(void *ptr, u64 align)
; align value must be a power of 2
_align:
    mov rax, rdi
    neg rdi
    dec rsi
    and rdi, rsi
    add rax, rdi
    ret

; the amount of memory for malloc to request at a time (must be a power of 2)
__malloc_step: equ 1 * 1024 * 1024 ; 1 MB
; alignment requirement of a malloc allocation (must be a power of 2)
__malloc_align: equ 16

; malloc linked list structure:
;            v initial sys brk (base of stack space)
; <--- stack | ([void *next][void *prev][... data ...])...
;              ^ doubly-linked list of zero or more malloc data blocks
; 
; we shall assume no one else will be manipulating memory beyond the initial breakpoint.
; the start of each block will be aligned to __malloc_align.
; bit 0 of the 'next' field will hold 1 if the block is occupied.
; 
; void *malloc(u64 size)
; allocates contiguous memory in dynamically-allocated space via sys_brk.
; you should not directly call sys_brk at any time (except in the case where it just returns the current break).
; the memory returned is aligned on 16-byte boundaries, making it suitable for all primitive types (including aligned xmm values).
; the pointer returned by this function must later be dealocated by calling free().
; allocating 0 bytes returns null.
; upon failure (e.g. sys_brk refused), returns null.
; upon success, returns a (non-null) pointer to the allocated memory, valid over the address space [0, size).
; dereferencing this pointer out of bounds is undefined behavior - importantly, this can corrupt the malloc data structure.
malloc:
    ; allocating 0 returns null
    cmp rdi, 0
    jnz .beg
    xor rax, rax
    ret
    
    .beg:
    ; align the request size
    mov esi, __malloc_align
    call _align
    mov rdi, rax
    
    ; get the beg/end positions
    mov rsi, [__malloc_beg]
    mov r8,  [__malloc_end]

    ; look through the list for an available block of sufficient size
    ; for(void *prev = 0, *pos = beg; pos < end; prev = pos, pos = pos->next)
    ; -- prev = r11
    ; -- pos = rsi
    ; -- end = r8
    xor r11, r11
    jmp .aft
    .top:
        ; get the next pointer
        mov rdx, [rsi]
        btr rdx, 0
        jc .cont ; if it's occupied, skip
        
        ; compute size - if it's not big enough, it won't work
        mov rcx, rdx
        sub rcx, rsi
        sub rcx, 16
        cmp rcx, rdi
        jb .cont ; if it's too small, skip it
        je .nosplit
        
        lea rax, [rsi + 16 + rdi] ; start of split
        mov [rax], rdx      ; update split's next (vacant)
        mov [rax + 8], rsi  ; update split's prev
        cmp rdx, r8
        cmovb [rdx + 8], rax ; if next is in bounds, update next->prev
        mov rdx, rax         ; update register that holds our next
        
        .nosplit:
        or dl, 1 ; mark this block as occupied
        mov [rsi], rdx
        lea rax, [rsi + 16] ; return pointer to data array
        ret
        
    .cont:
        mov r11, rsi
        mov rsi, rdx
    .aft:
        cmp rsi, r8
        jb .top
    
    ; -- if we got here, we went out of range of the malloc field -- ;
    
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
    bts r10, 0
    mov [r8], r10
    mov [r8 + 8], r11
    lea rax, [r8 + 16]
    ret
    
    .nospace:
    ; otherwise we have no space - allocate more to make new break (r10) valid
    mov rcx, rdi
    mov rdi, r10
    mov rsi, __malloc_step
    call _align
    mov rbx, rax
    mov eax, sys_brk
    syscall
    mov rdi, rcx

    ; if we got a zero return, we're good
    cmp rax, 0
    jz .enough_space
    ; otherwise it failed - return null
    xor rax, rax
    ret

; void *realloc(void *ptr, qword size)
; creates a new aray with the specified size and copies over the contents.
; the resulting array is identical up to the lesser of the two sizes.
; if posible, the resize is performed in-place.
; returns a pointer to the new array.
; reallocating a null pointer is equivalent to calling malloc()
; reallocating to a size of zero is equivalent to calling free() (and returns null).
realloc:
    ; if pointer is null, call malloc()
    cmp rdi, 0
    cmovz rdi, rsi
    jz malloc
    
    ; if size is zero, call free()
    cmp rsi, 0
    jnz .resize
    call free
    xor rax, rax ; we need to return null
    ret
    .resize:
    
    ; align the size (for later)
    mov r8, rdi
    mov rdi, rsi
    mov esi, __malloc_align
    call _align
    mov rsi, rax ; aligned size back in rsi
    mov rdi, r8  ; pointer back in rdi
    
    ; compute the size of this block
    mov rcx, [rdi - 16]
    btr rcx, 0
    mov rbx, rcx ; save a copy of next in rbx
    sub rcx, rdi
    
    ; if we already have enough space, we're good
    cmp rcx, rsi
    jae .enough_space
    ; compute the smaller size into rcx
    cmova rcx, rsi
    
    ; we now know we're resizing to be larger - decide what we can do
    cmp rbx, [__malloc_end]
    je .inplace_tail ; if next is __malloc_end we can do it in-place as a tail extension
    mov r11, [rbx] ; next->next in r11
    btr r11, 0
    jc .new_array ; if next is occupied, we need a new array
    sub r11, rdi ; compute size of merging with (vacant) bucket to the right
    cmp r11, rsi
    jae .inplace_merge ; if merged has enough space, we can still do it inplace
    jmp .new_array ; otherwise we need a new array

    .inplace_tail:
    mov eax, sys_brk
    xor ebx, ebx
    syscall             ; current break point in rax
    lea r8, [rdi + rsi] ; break point needed in r8 (this is why we aligned size earlier)
    
    ; if we have enough room, just move __malloc_end
    cmp r8, rax
    ja .more_mem
    
    .good_mem:
    mov [__malloc_end], r8
    or r8b, 1
    mov [rdi - 16], r8
    mov rax, rdi
    ret
    
    .more_mem:
    ; otherwise we need to allocate more space to make new break (r8) valid
    mov r10, rdi
    mov rdi, r8
    mov rsi, __malloc_step
    call _align
    mov rbx, rax
    mov eax, sys_brk
    syscall
    mov rdi, r10
    
    ; if it succeeded, we're done
    cmp rax, 0
    jz .good_mem
    ; otherwise it failed - return null
    xor rax, rax
    ret
    
    .inplace_merge:
    lea rax, [rdi - 16] ; my meta block
    mov rcx, [rbx]      ; next->next in rcx (at this point next is guaranteed to be vacant)
    mov [rax], rcx
    bts qword ptr [rax], 0
    mov [rcx + 8], rax
    sub rcx, rdi
    jmp .enough_space ; we've now merged with the vacant block, so we can just truncate this expanded block

    .new_array: ; sad days, everybody, we need a new array
    push rcx
    push rdi
    mov rdi, rsi
    call malloc
    mov rdi, rax ; new array in rdi
    pop rsi      ; old array in rsi
    pop rcx      ; smaller size in rcx
    
    ; copy the contents up to the smaller size (this is why we aligned the size earlier)
    shr rcx, 3
    cld
    push rdi
    push rsi
    rep movsq
    pop rsi
    pop rdi

    ; free the old array
    push rdi
    mov rdi, rsi
    call free
    pop rax
    ret
    
    .enough_space: ; rcx has (full) size of this block, rsi has aligned requested size (less than or equal to block size), rdi has allocated pointer
    cmp rcx, rsi
    je .no_split
    lea r8, [rdi - 16]       ; my meta block
    lea r9, [rdi + rsi]      ; split point meta block
    mov rax, [r8]            ; rax is my meta next (has the occupied flag)
    mov [r8], r9             ; my next is the split block
    bts qword ptr [r8], 0    ; mark myself as allocated (in-place realloc)
    mov [r9], rax            ; split next is my meta next (occupied because we are occupied - then we'll free it to perform the merge operation)
    mov [r9 + 8], r8         ; split prev is my meta block
    cmp rax, [__malloc_end]  ; make sure next line is in bounds
    cmovb [rax - 1 + 8], r9  ; split->next->prev = split   PROBLEM HERE
    push rdi
    lea rdi, [r9 + 16]
    call free ; free the split block (marked as allocated) to perform any required merging and pruning operations
    pop rax
    ret

    .no_split:
    mov rax, rdi
    ret

; void free(void *ptr)
; deallocated resources that were allocated by malloc/calloc/realloc.
; the specified pointer must be exactly what was returned by the allocation function.
; freeing the same allocation twice is undefined behavior.
; freeing null is no-op.
free:
    cmp rdi, 0
    jz .ret

    ; get the meta block
    sub rdi, 16
    ; get next in rdx
    mov rdx, [rdi]
    btr rdx, 0
    ; if next is in range and not in use, get next->next in rdx (we'll merge right)
    cmp rdx, [__malloc_end]
    jae .nomerge_right
    mov rcx, [rdx]
    bt rcx, 0
    cmovnc rdx, rcx
    .nomerge_right:
    
    ; get prev in rcx
    mov rcx, [rdi + 8]
    ; if prev is in range and not in use, merge with it
    cmp rcx, 0
    jz .nomerge_left
    bt qword ptr [rcx], 0
    jc .nomerge_left
    mov rdi, rcx
    .nomerge_left:

    ; perform all the merging we need
    mov [rdi], rdx           ; update our next pointer
    cmp rdx, [__malloc_end]  ; check for the end pointer condition
    cmovne [rdx + 8], rdi    ; rdx could be the end pointer, in which case don't dereference it (could be out of bounds)
    jne .ret                 ; if our updated next pointer is not the end pointer, we're done
    mov [__malloc_end], rdi  ; otherwise eliminate this block from the list
    .ret: ret

; void *calloc(qword size)
; as malloc except that it also zeroes the contents.
calloc:
    call malloc
    cmp rax, 0
    jz .ret ; if allocation failed, early return
    mov r8, rax
    mov rdi, rax
    xor rax, rax
    mov rcx, [rdi - 16] ; remember there's a state flag in bit 0 of this value
    sub rcx, rdi
    shr rcx, 3 ; division by 8 discards the state flag, so we're ok
    cld
    rep stosq
    mov rax, r8
    .ret: ret

segment bss

align 8 ; begin/end address for malloc data structure - these must be initialized before use
__malloc_beg: resq 1
__malloc_end: resq 1
