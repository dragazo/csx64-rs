# CSX64 Standard Library

CSX64 is meant to be a highly-realistic educational tool for learning assembly.
Because of this, only real-world instructions and system calls are provided, which means you would be on your own for doing things like string formatting and dynamic memory allocation.
However, because this would be unbearable to use outside of a one-off academic exercise, a CSX64 assembly implementation of (a subset of) the C standard library is included (in this directory).

## Calling Conventions

If you intend to use the CSX64 stdlib files, you'll need to know how it handles arguments and return values.
These conventions will be based on a hypothetical equivalent C-style function signature `res foo(arg1, arg2, arg3, etc.)`.

When calling a function, integer arguments (signed, unsigned, or pointer values) go in `rdi`, `rsi`, `rdx`, `rcx`, `r8`, `r9` (in that order).
Floating point values are placed in the (scalar portions) of `xmm0`, `xmm1`, `xmm2`, ..., `xmm7`.
Any arguments which can't be put in a register because you ran out of registers (e.g. your 7th integral value or 9th floating-point value) must be pushed onto the stack in reverse order of their C-style function declaration (so that they are in the correct ascending order in the address space).
Integer return values are placed in `rax`, and floating-point return values are placed in (the scalar portion of) `xmm0`.

There is currently no convention for taking or returning a value which is too large to fit in a register (because assembly lacks structures), so that decision is up to you.
But no functions in the stdlib need this, so your decision doesn't affect anything but your own code.


## Call-safe registers

When you call a function, it might use some registers to perform its calculation.
Because of this, a value you have in a register before calling a function might be destroyed by the time the function returns.
To fix this, you can push the register onto the stack before the function call and reload it afterwards.

However, this is annoying and can hurt performance.
Because of this, it is guaranteed that `r12`, `r13`, `r14`, and `r15` will not be modified by the time a function returns.
This means you can safely use them and call functions, without fear of their values being destroyed.

But this guarantee has a cost: you must also guarantee that any function you write will preserve the value of these registers by the time you return.
The easiest way to do this is to simply not use them if you can avoid it, but you could also push them onto the stack and restore them before you return.
The following is an example of typical use:

```asm
foo:
    push r15 ; we need to use r15, so store previous value

    ... do whatever you need

    pop r15 ; restore the old value before returning
    ret
```

If you have a function which has many return points, it can be difficult to make sure you restore the call-safe registers at every return point.
In this case, you may prefer to make the function private and create a safe wrapper around it, which only has one return point.
Here's an example:

```asm
_foo: ; private function that does not preserve call-safe registers
    mov r15, 354
    ...

    .case0:
    ...
    ret ; possible return point

    .case1:
    ...
    ret ; another return point

    .case2:
    ...
    ret ; another... etc.

foo: ; safe wrapper for _foo which preserves registers
    push r15  ; save the register value
    call _foo ; invoke the unsafe version
    pop r15   ; restore before returning
    ret
```

## Calling Variadic functions

In C, there is a notion of functions which take a variable number of arguments.
This is denoted by `'...'` in the arguments list; for instance, `int printf(const char *fmt, ...)`.

The calling convention for a variadic function is almost identical to a normal function, except that you have to extend each argument to 64-bits.
For instance, to call `printf("%f", 4.5f)` (passing a 32-bit float), you should extend `4.5` to 64-bits and place it in `xmm0`.
Similarly, if you pass a 32-bit integer you should extend it to 64-bits and place it in whatever integer register it should go in based on argument order.
Note that if you have many arguments and some must go on the stack, they must still be extended to 64-bit.

Some functions don't require this extension for some types; for instance `printf("%c", 'H')` happens to ignore the upper bits of the `'H'` argument, so you technically don't have to extend it in this case.

## Writing Variadic Functions

Not finalized yet.