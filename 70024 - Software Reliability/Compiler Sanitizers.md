## Definition
Instrument code at compile time (static instrumentation) to analyse at runtime.
- Some cannot be combined (e.g. MSan and ASan)
- Much faster than dynamic instrumentation of binaries (e.g. [[Valgrind]])
## Clang/GCC Sanitizers
### Address Sanitizer
```bash
-fsanitize=address
```
- Detects out of bounds accesses, use after free, and memory leaks. 
- Typically $\approx2\times$ slowdown.
- Adds red-zones around all allocations (marked as poisoned), and after frees. If poisoned addresses are accessed, then throws an error, backtrace and printout of accessed poisoned buffer.

#### Poisoning
Poisoning is done with their own version of malloc on the heap, and by adding to stack frames (extra pushes/pops added at compile time). BSS has redzones added at compile time also.

When memory is freed it is put in *quarantine* (a limited size FIFO), when accessed.
- Limited size $\to$ large distance means access not detected.
#### Shadow Memory
(Also used in [[Valgrind]]), each byte is associated with some memory containing metadata.
- On each memory access, check its shadow exists (create if not)
Each 8 bytes (assumes 8 byte alignment) encoded with 9 states held in a single byte:

| State | Meaning |
| ---- | ---- |
| $=0$ | All bytes addressable |
| $<0$ | No bytes Addressable |
| $1 \leq k \leq 7$ | $k$ bytes addressable |
```rust
unsafe fn to_shadow(addr: *u8) -> *u8 {
	SHADOWN_REGION_OFFSET + (addr / 8)
}
```
#### Results
No false positives, some false negatives (overflow bypasses redzones, large time distance between free and use after free). 
### Memory Sanitizer
```bash
-fsanitize=memory
```
Detects uninitialized memory accesses. Typically $\approx3\times$ slowdown.
#### Shadow Memory
Each byte is mapped to a single *validity bit*, declaring if it is initialised.
#### Results
Not all reads uninitialized are bad.
```c
int a, b;
a = b; // value ignored, so no need to report 
a = 1;
```

Hence it is restricted to:
- reads in branch conditions
- reads for determining memory accesses
- reads passed to system calls
It's reports have:
- false positives when interacting with uninstrumented code 
- allows for annotations to declare safe objects in source, to avoid reporting

## Undefined Behaviour Sanitizer
Detects a set of undefined behaviours.
[UndefinedBehaviorSanitizer — Clang 19.0.0git documentation (llvm.org)](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html)

## Thread Sanitizer
Detects data races and deadlocks. Typically $\approx5-15\times$ slowdown.