## Definition
A series of nop instructions used to capture any jump to the sled of instructions, and allow the program counter to descend the sled to some code.
```
nop
nop
nop  <- jumping to any instruction on the sled leads to <code>
nop
nop
nop
<code>
```