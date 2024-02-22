## Attacks
### Code Corruption
An attempt to modify code in memory.
- For elf binaries pages containing code are marked as readonly, and the heap and stack marked as non-executable. But this does not prevent modification of interpreted bytecodes stored on the heap.
- Systems using code generation (e.g. JIT) need pages that are readable, writable and executable, so cannot use the same protections.
### Control Flow Hijack
Corrupt pointers used for control flow (e.g. return address, function pointers, vtables) to direct control flow.
### Non-Control-Data Attacks
Corrupt security related data (not code).
```c
void authenticate(int input) {
	char auth = 0; 
	char buf[128] = {0};
	// depending on layout of local vars on stack, an overflow to 
	// buf can overwrite auth
	buf[input] = 1;
	if (auth) {
		set_privileged_mode();
	}
}
```
This also includes dangling pointers left after freeing, that can be used to access data allocated in the same location later, and potentially to corrupt.
### Leak Confidential Memory
Out of bounds reads on buffers. 
[Heartbleed - Wikipedia](https://en.wikipedia.org/wiki/Heartbleed)
## Defences
### Stack Canaries
Compiler adds canaries (a magic value) into stack frames, and verifies integrity at start and end of call to ensure no corruption has occurred. If the canary is valid, it is likely no stack corruption occurred.

Common values include `\0` / null (e.g. to prevent null terminated string copy/access from overflowing).
