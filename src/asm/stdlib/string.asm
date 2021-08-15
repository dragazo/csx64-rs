; source = http://www.cplusplus.com/reference/cstring/
; todo: strcoll (these 2 are less important)
;       strxfrm
;
;       strtok
;       

global memcpy
; global memmove
; global strcpy
; global strncpy
; global strlen

; global strcat
; global strncat

; global memcmp
; global strcmp
; global strncmp

; global memchr
; global strchr
; global strrchr
; global strcspn
; global strspn
; global strstr
; global strpbrk

; global memset
; global strerror

; ----------------------

segment text

; void *memcpy(void *dest, const void *src, size_t num);
memcpy:
    ; copy dest into rax (for return value)
    mov rax, rdi
    
    ; copy the data
    mov rcx, rdx
    cld
    rep movsb
    
    ret

; ; void *memmove(void *dest, const void *src, sizt_t num);
; memmove:
;     mov rax, rdi ; copy dest into rax (for return value)
;     mov rcx, rdx ; move num into rcx
    
;     ; pick a copy direction
;     cmp rdi, rsi
;     ja .backwards
    
;     ; -- forward copy -- ;
    
;     cld
;     rep movsb
;     ret
    
;     ; -- backward copy -- ;
;     .backwards:
    
;     ; modify dest/src to point to the last element in the copy range
;     lea rdi, [rdi + rcx - 1]
;     lea rsi, [rsi + rcx - 1]
    
;     std
;     rep movsb
;     ret

; ; size_t strlen(const char *str);
; strlen:
;     ; store str in r8 for safekeeping
;     mov r8, rdi
    
;     ; skip all nonzero bytes
;     cld
;     xor rax, rax
;     mov rcx, -1
;     repne scasb
;     ; rdi is now 1 past the first zero byte
    
;     ; return length of string
;     lea rax, [rdi - 1]
;     sub rax, r8
;     ret

; ; char *strcpy(char *dest, const char *src);
; strcpy:
;     mov rax, rdi ; store dest in rax (for return value)
    
;     xor rcx, rcx
;     .top:
;         ; copy a char
;         mov bl, [rsi + rcx]
;         mov [rdi + rcx], bl
        
;         inc rcx
        
;         ; if char was non-zero, repeat
;         cmp bl, 0
;         jne .top
    
;     ; return dest
;     ret

; ; char *strncpy(char *dest, const char *src, size_t num);
; strncpy:
;     mov r8, rdi ; store dest in r8 for safekeeping
    
;     ; for(i = 0; i < num; ++i)
;     xor rcx, rcx
;     jmp .aft
;     .top:
;         ; dest[i] = src[i]
;         mov al, [rsi + rcx]
;         mov [rdi + rcx], al
        
;         ; PRE-increment (important)
;         inc rcx
        
;         ; if char was nonzero, continue
;         cmp al, 0
;         jne .aft
;         ; otherwise pad with zeros to end and return
;         cld
;         add rdi, rcx
;         sub rdx, rcx
;         mov rcx, rdx
;         rep stosb ; (AL already contains zero)
;         jmp .ret
        
;     .aft:
;         cmp rcx, rdx
;         jb .top
    
;     ; return dest
;     .ret:
;     mov rax, r8
;     ret

; ; char *strcat(char *dest, const char *src);
; strcat:
;     push rdi ; push dest for safekeeping
    
;     ; skip past the null term in dest
;     cld
;     xor rax, rax
;     mov rcx, -1
;     repne scasb
;     ; rdi is now 1 past null term - dec to point at null
;     dec rdi
    
;     ; use strcpy to perform the cat
;     call strcpy
    
;     ; return dest
;     pop rax
;     ret
    
; ; char *strncat(char *dest, const char *src, size_t num);
; strncat:
;     push rdi ; push dest for safekeeping
    
;     ; skip past the null term in dest
;     cld
;     xor rax, rax
;     mov rcx, -1
;     repne scasb
;     ; rdi is now 1 past null term - dec to point at null
;     dec rdi
    
;     ; append at most num bytes
;     xor rcx, rcx
;     jmp .aft
;     .top:
;         ; dest[i] = src[i]
;         mov al, [rsi + rcx]
;         mov [rdi + rcx], al
        
;         ; if we copied a null, we're done
;         cmp al, 0
;         jz .ret
        
;     .aft:
;         cmp rcx, rdx
;         jb .top
    
;     ; if we get here, we hit the num limit - append the null terminator
;     mov byte ptr [rdi + rcx], 0
    
;     ; return dest
;     .ret:
;     pop rax
;     ret
    
; ; int memcmp(const void *ptr1, const void *ptr2, size_t num);
; memcmp:
;     ; if (num == 0) return 0
;     cmp rdx, 0
;     jz .ret_z
    
;     ; run past all the equal bytes
;     cld
;     mov rcx, rdx
;     repe cmpsb
;     ; we're now 1 past the end (if all equal) or 1 past the first different byte
    
;     ; return the difference sign extended to 32-bit
;     mov al, [rdi - 1]
;     sub al, [rsi - 1]
;     movsx eax, al
;     ret
    
;     .ret_z: ; return zero
;     xor rax, rax
;     ret

; ; int strcmp(const char *str1, const char *str2); // ret >0 -> str1 > str2
; strcmp:
;     ; for(int count = 0; ; ++count)
;     xor rcx, rcx ; zero count
;     .top:
;         mov al, [rdi + rcx] ; get str1 byte (a)
;         mov bl, [rsi + rcx] ; get str2 byte (b)
        
;         ; if (a == 0) return b
;         cmp al, 0
;         movz al, bl
;         jz .ret_diff
        
;         ; if (b == 0_ return -a
;         mov r8b, al
;         neg r8b
;         cmp bl, 0
;         movz al, r8b
;         jz .ret_diff
        
;         ; if (a - b != 0) return a - b
;         sub al, bl
;         cmp al, 0
;         jnz .ret_diff
        
;         ; inc count
;         inc rcx
;         jmp .top
    
;     .ret_diff:
;         ; sign extend difference to 32-bit
;         movsx eax, al
;         ret
        
; ; int strncmp(const char *str1, const char *str2, size_t num); // ret >0 -> str1 > str2
; strncmp:
;     ; for(int count = 0; count < num; ++count)
;     xor rcx, rcx ; zero count
;     jmp .aft
;     .top:
;         mov al, [rdi + rcx] ; get str1 byte (a)
;         mov bl, [rsi + rcx] ; get str2 byte (b)
        
;         ; if (a == 0) return b
;         cmp al, 0
;         movz al, bl
;         jz .ret_diff
        
;         ; if (b == 0) return -a
;         mov r8b, al
;         neg r8b
;         cmp bl, 0
;         movz al, r8b
;         jz .ret_diff
        
;         ; if (a - b != 0) return a - b
;         sub al, bl
;         cmp al, 0
;         jnz .ret_diff
        
;         inc rcx
;     .aft:
;         cmp rcx, rdx
;         jb .top
    
;     .ret_same:
;         ; zero return val
;         xor eax, eax
;         ret
    
;     .ret_diff:
;         ; sign extend difference to 32-bit
;         movsx eax, al
;         ret 
        
; ; void *memchr (void *ptr, int value, size_t num);
; memchr:
;     ; if (num == 0) return null;
;     cmp rdx, 0
;     jz .no_match
    
;     ; skip past all the unequal bytes
;     mov rax, rsi
;     mov rcx, rdx
;     cld
;     repne scasb
;     ; rdi is now either 1 past end (none found) or 1 past first occurrence of value
    
;     ; if we didn't find one, return null
;     jne .no_match
;     ; otherwise return its address
;     lea rax, [rdi - 1]
;     ret
    
;     .no_match:
;     xor rax, rax
;     ret
    
; ; char *strchr (char *str, int character);
; strchr:
;     .top:
;         ; get a character
;         mov al, [rdi]
        
;         ; if it's the value, return str
;         cmp al, sil
;         move rax, rdi
;         je .ret
        
;         ; if it's a null, we're done searching
;         cmp al, 0
;         je .ret_null
        
;         ; inc str and on to next char
;         inc rdi
;         jmp .top
        
;     .ret_null: xor rax, rax
;     .ret: ret

; ; char *strrchr (char *str, int character);
; strrchr:
;     push rdi
;     push rsi
;     call strlen ; get string length
;     pop rsi
;     pop rdi
    
;     ; store str pointer in rbx
;     mov rbx, rdi
;     ; make rdi point to end of string
;     add rdi, rax
;     dec rdi
    
;     .top:
;         ; get a character
;         mov al, [rdi]
        
;         ; if it's the value, return str
;         cmp al, sil
;         move rax, rdi
;         je .ret
        
;         ; if back at start of string, we're done searching
;         cmp rdi, rbx
;         je .ret_null
        
;         ; dec str and on to next char
;         dec rdi
;         jmp .top
        
;     .ret_null: xor rax, rax
;     .ret: ret

; ; size_t strcspn(const char *str1, const char *str2);
; strcspn:
;     ; look through each character in str1
;     xor rax, rax
;     .str1.top:
;         mov cl, [rdi + rax] ; str1 char
        
;         ; look through each character in str2
;         xor rbx, rbx
;         .str2.top:
;             mov dl, [rsi + rbx] ; str2 char
            
;             ; if this is a match, return index in str1
;             cmp dl, cl
;             je .ret
            
;             ; if st2 char is non-null, loop in str2
;             inc rbx
;             cmp dl, 0
;             jnz .str2.top
;         ; loop in str1
;         inc rax
;         jmp .str1.top
        
;     .ret: ret
        
; ; size_t strspn(const char *str1, const char *str2);
; strspn:
;     ; look through each character in str1
;     xor rax, rax
;     .str1.top:
;         mov cl, [rdi + rax] ; str1 char
        
;         ; look through each character in str2
;         xor rbx, rbx
;         .str2.top:
;             mov dl, [rsi + rbx] ; str2 character
            
;             ; if str2 char is null, we failed to match - return index in str1
;             cmp dl, 0
;             je .ret
            
;             ; if it matches, loop in str1
;             cmp dl, cl
;             je .str1.aft
            
;             ; loop in str2
;             inc rbx
;             jmp .str2.top
;         .str1.aft:
;         ; loop in str1
;         inc rax
;         jmp .str1.top
        
;     .ret: ret

; ; char *strstr(const char * str1, const char * str2);
; strstr:
;     ; for each position in str1
;     .str1.top:
;         ; look for a match with str2
;         xor rax, rax
;         .match.top:
;             mov cl, [rdi + rax] ; str1 char
;             mov dl, [rsi + rax] ; str2 char
            
;             ; if str2 char is null, we found a match
;             cmp dl, 0
;             jz .ret
            
;             ; if str1 char is null, return null
;             cmp cl, 0
;             jz .ret_null
            
;             ; otherwise, if they don't match, loop in str1
;             cmp cl, dl
;             jne .str1.aft
            
;             ; they matched - loop in match
;             inc rax
;             jmp .match.top
;         .str1.aft:
;         inc rdi
;         jmp .str1.top
    
;     .ret_null: xor rax, rax
;     .ret: ret

; ; char *strpbrk(const char *str1, const char *str2);
; strpbrk:
;     ; for each character in str1
;     .str1.top:
;         mov cl, [rdi] ; str1 char
        
;         ; if str1 char is null, return null
;         cmp cl, 0
;         jz .ret_null
        
;         ; look for a match in str2
;         xor rcx, rcx
;         .match.top:
;             mov dl, [rsi + rcx] ; str2 char
            
;             ; if str2 char is null, no match - loop in str1
;             cmp dl, 0
;             jz .str1.aft
            
;             ; if it doesn't match, loop in match
;             cmp cl, dl
;             jne .match.aft
            
;             ; otherwise they match - return pointer in str1
;             mov rax, rdi
;             ret
            
;             .match.aft:
;             inc rcx
;             jmp .match.top
            
;         .str1.aft:
;         inc rdi
;         jmp .str1.top
    
;     .ret_null: xor rax, rax
;     .ret: ret
    
; ; void *memset(void *ptr, int value, size_t num);
; memset:
;     mov r8, rdi ; copy ptr to r8 for safekeeping
    
;     ; fill in the values
;     cld
;     mov rax, rsi
;     mov rcx, rdx
;     rep stosb
    
;     ; return ptr
;     mov rax, r8
;     ret
    
; ; const char *strerror(int errnum);
; strerror:
;     ; return PLACEHOLDER
;     mov rax, $str("errno_NOTIMPLEMENTED")
;     ret
    


	