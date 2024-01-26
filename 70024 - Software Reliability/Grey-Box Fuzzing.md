## Definition
Instrumentation is applied to the [[SUT]] to provide information about internals (e.g. coverage, [[Compiler Sanitizers]] for behaviour).
- Can be done at compile time, or binaries with debug & relocation information can be instrumented
### Advantages
- More feedback for [[Feedback-Directed Fuzzing]]
### Disadvantages
- Instrumentation decreases binary performance
- Compile-time instrumentation requires the [[SUT]] source