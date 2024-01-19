## Definition
A [[Soft Processor]] supporting a 32-bit [[RISC]] architecture, 32 interrupt sources, and optional single-precision floating point operations.

Functional units can be implemented in hardware, emulated in software (e.g. implement floating point multiplication using fixed point instructions for using [[NIOS II]] functional units), or omitted entirely.

| Core Design | Description |
| ---- | ---- |
| Nios II/f | Fast performance (large size) |
| Nios II/s | Balance between *e* and *f* |
| Nios II/e | Economy core (small size)  |
## Units
### ALU
| Operation | Description |
| ---- | ---- |
| Arithmetic | `+,-,/` on unsigned integers |
| Relational | Comparison operations for `==,!=,>=,<` on signed & unsigned integers |
| Shift/Rotate | `0-31` positions per instruction, arithmetic right shift & logical right/left shift. |
*Arithmetic right means shift right, and fill empty left with MSB (hence preserving sign also)*
### Cache
On chip separate instruction and data caches.
- Caches are optional for example when all data and instructions are stored on chip memory (the cache is used for caching external memory, no longer needed)
- Instruction cache is not effective if instruction cache is much smaller than the working set of instructions (e.g. 2KB hot loop, with 1KB instruction cache)
### Tightly Coupled Memory
A guaranteed low-latency memory on chip.
- No need for cache, so no overhead from using a cache.
- performance of the memory is similar to cache hit.
- Cannot be adapted to dynamic behaviour - a fixed region of the available address space is mapped to this memory.
- Place fast access data/instructions here (e.g. performance critical interrupt code)