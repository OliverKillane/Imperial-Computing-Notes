## [Smashing the Gadgets: Hindering Return-Oriented Programming Using In-Place Code Randomization](https://comp97109.doc.ic.ac.uk/reading/smashing-rop.pdf)
## Summary
This paper summarises the capabilities and limitations of a code randomization tool called `orp`.
The tool randomizes gadgets that could be used for `ROP` by changing the executable in-place, meaning offsets for data access, jumps etc do not need to be modified, and the tool can therefore work one executables with no relocation information available.

The restricted nature of the randomizations (for individual instructions, intra-basic-block instruction reordering, register reassignment and limited stack reordering for calling-convention preserved values), means there is no detectable (in their benchmarks) performance degradation, and it is still effective against ROP (even when unable to randomize all gadgets) as only a single gadget used in a ROP program needs to be randomized to prevent it from working as intended.
## Pros
1. The restricted nature of the optimisations also excludes most that would affect performance (e.g. increasing the number of instructions, or modifying short to long `jmp`s due to reordering, ). The only potentially effectful transformation is the intra-basic-block instruction reordering, but even with this _*"in all cases, there was no observable difference"*_ in the runtime between original and randomized DLLs (share libraries). The paper does not detail how many randomised versions were used, for testing _*"multiple randomized versions"*_ were used (no further explanation).
2. No debugging information is required, so binaries can be randomized without source available, without developer's involvement (to distribute extra debug/relocation information), and thus the tool can be immediately put to use.
3. No debugging information is required, so optimised and stripped binaries can have their gadgets smashed, again not compromising on performance.
4. The paper bases the effectiveness of the limited transformations against ROP on the fragility of ROP code. If even one gadget in the chain is compromised, the entire ROP program is. Using randomization none of their provided test cases for Mona and [Q](https://edmcman.github.io/papers/usenix11.pdf) compiled ROP programs could successfully run.
5. The same techniques used (in place mutation) on IA32, can be applied similarly to other architectures (e.g. arm, powerpc), and across operating systems as there are no OS-specific address space layout requirements as with other techniques.
## Cons

1. One of the key reasons behind their more restricted (no metamorphosis or inter-basic block reordering) is the lack of debug information available. This could be easily avoided by asking developers to distribute obfuscated binaries which still contain relocation information. Or even better to distribute the binary in a serialized version of this tool's internal format, to allow quick randomization for users.
2. When determining data dependencies between instructions, all non-trivial (e.g. absolute) memory address accesses are considered potentially equal. *"In our future work, we plan to use simple data flow analysis to relax this condition."*
3. The analysis assumes basic block boundaries do not change at runtime. This appears to mean they do not account for jumps to addresses determined at runtime, which seems to therefore ignore switch statements that typically use `jmp *base(, %val, ptr_size)` .  _"Although this may seem restrictive, we note that throughout our evaluation we did not encounter any such case"_ does not confidently assert correctness, but rather that there were no cases where the gadget elimination affected the initial jump for a switch statement. 
4. Only supports 32-bit PE (Microsoft windows) executables despite being published in 2012.
5. Packed executables cannot be modified directly (the technique's intention is to make reverse-engineering more difficult), and the technique cannot be applied to programs that perform self-integrity checks (e.g. checking their own code is unmodified using a checksum)
## Things to Improve
1. Add in dataflow analysis to improve the aforementioned limiting assumptions on memory accesses (must assume all accesses by non-immediate could be to the same location when determining data dependencies between instructions).
2. Support for ELF binaries (linux). Quite a small change as `orp`'s core only deals with x86 binary code & semantics, and does not rely on debug (PDB), or relocation information that is PE only.
3. Support for x86_64, this is important as the vast majority of x86 devices sold, and currently popular applications for x86 are 64 bit.
4. Greater testing, as per the [[Smashing the Gadgets#Cons|cons]] it is mentioned that the analysis `orp` uses assumes no changes to basic block boundaries, even though this is not always true. Testing for correct behaviour of more programs would provide more assurance, than the 5,235 PE files it was tested on.
5. *Slightly strange suggestion:* they have effectively created a mutation [[Fuzzing|fuzzer]], though this perspective is not mentioned at all in the paper. The ability to fuzz a CPU with random permutations of any available 32-bit PE binary or shared-lib (DLL) for differences in behaviour (expected to be the same) or performance (expected to be the same).