; contract: these functions may only modify eax and edi (and flags)
global isalpha, islower, isupper, isdigit
global isalnum, isxdigit 
global iscntrl, isspace, isblank
global isprint, isgraph, ispunct

; contract: these functions may only modify eax, edi, and esi (and flags)
global tolower, toupper

segment text

; int isalpha(int)
isalpha:
    or dil, 32 ; convert to lowercase
; int islower(int);
islower:
    sub dil, 'a'
    cmp dil, 26 ; a-z
    setb eax
    ret
; int isupper(int)
isupper:
    sub dil, 'A'
    cmp dil, 26 ; A-Z
    setb eax
    ret
; int isdigit(int)
isdigit:
    sub dil, '0'
    cmp dil, 10 ; 0-9
    setb eax
    ret

; int isalnum(int)
isalnum:
    mov eax, edi ; store char in eax
    or  dil, 32  ; convert to lowercase
    sub dil, 'a'
    cmp dil, 26  ; a-z or A-Z
    mov edi, eax ; restore char to eax
    jae isdigit  ; if not in char range, refer to isdigit
    mov eax, 1
    ret
; int isxdigit(int)
isxdigit:
    mov eax, edi ; store char in eax
    or  dil, 32  ; convert to lowercase
    sub dil, 'a'
    cmp dil, 6   ; a-f or A-F
    mov edi, eax ; restore char to eax
    jae isdigit  ; if not in char range, refer to isdigit
    mov eax, 1
    ret

; int iscntrl(int)
iscntrl:
    cmp dil, 0x20 ; main control block
    jae .other
    mov eax, 1
    ret
    .other: cmp dil, 0x7f ; or DEL
    sete eax
    ret
; int isspace(int)
isspace:
    sub dil, 9 ; main space block
    cmp dil, 5
    jae .other
    mov eax, 1
    ret
    .other: cmp dil, 0x20-9 ; actual ' ' char
    sete eax
    ret
; int isblank(int)
isblank:
    cmp dil, 9 ; tab
    jne .other
    mov eax, 1
    ret
    .other: cmp dil, 0x20 ; space ' '
    sete eax
    ret
    
; int isprint(int)
isprint:
    cmp dil, 0x20
    jb .ret_0
    cmp dil, 0x7f
    setne eax
    ret
    .ret_0: xor eax, eax
    ret
; int isgraph(int)
isgraph:
    cmp dil, 0x21
    jb .ret_0
    cmp dil, 0x7f
    setne eax
    ret
    .ret_0: xor eax, eax
    ret
; int ispunct(int)
ispunct:
    call isgraph ; must be a graph char
    cmp eax, 0
    jz .ret
    call isalnum ; must not be alnum
    cmp eax, 0
    setz eax
    .ret: ret

; int tolower(int)
tolower:
    mov esi, edi ; store char in esi
    call isupper
    cmp eax, 0
    jz .ret
    or sil, 32 ; convert to lower
    .ret: mov eax, esi
    ret
; int toupper(int)
toupper:
    mov esi, edi ; store char in esi
    call islower
    cmp eax, 0
    jz .ret
    and sil, !32 ; convert to upper
    .ret: mov eax, esi
    ret