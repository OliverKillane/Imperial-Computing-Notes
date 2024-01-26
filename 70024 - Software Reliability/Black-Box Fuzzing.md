## Definition
The [[SUT]] is executed in an unmodified form (no sanitizers or coverage added).
### Advantages
- Can be applied to closed source [[SUT]]
- [[SUT]] can run at full speed (optimized binary), enabling a higher rate of fuzzing
### Disadvantages
- Feedback directed fuzzing can only make use of externally-visible [[SUT]] behaviour (cannot augment [[SUT]] with coverage)