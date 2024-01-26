## Definition
[[Program Analysis]] using constraint solving to generate inputs that provable cover different parts of the [[SUT]].
- Called [[Symbolic Execution]], and is only loosely definable as [[Fuzzing]]
### Advantages
Constraint solving ensures a minimal set of inputs (fast to run, slow to generate) that can perfectly cover entire [[SUT]], including inputs that are extremely unlikely to occur under random testing.
### Disadvantages
- Limited scalability due to solving overhead
- Requires specialized toolchain