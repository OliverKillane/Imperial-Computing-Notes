## Definition
Forcing a jump to a gadget (a section of code already included & executable within a binary, ending in a return statement) by abusing the saved return pointer on the stack to force a jump to said code on return (i.e. loading that value from stack to the link register and executing a return instruction, or a jump to said register).

By building up a stack of return values these gadgets can be chained together.

Automatic tools for compiling return oriented code have been developed, such as Mona and [Q](https://edmcman.github.io/papers/usenix11.pdf). Gadgets can be found with tools like [ROPgadget](https://github.com/JonathanSalwan/ROPgadget).
## Preventative Measures
Tools to break gadgets (see [[Smashing the Gadgets]]), and types of [[Address Space Layout Randomisation]]
## Examples
[[Return to libc]]