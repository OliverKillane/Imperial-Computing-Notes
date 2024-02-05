## Description
The original [[Return Oriented Programming]] exploit, as `libc` is almost always linked, it takes advantage of gadgets present in `libc`.

Many of these gadgets are powerful as `libc` contains useful calls from os-interaction.

For example
```python
Stack:
...
address of system() in libc
return from system()        <- EIP
address of string "/bin/sh" <- ESP
...
```
On return instruction, we jump to system with the string argument on the stack (hence running a new shell), on return from system() we are once again redirected to another address.