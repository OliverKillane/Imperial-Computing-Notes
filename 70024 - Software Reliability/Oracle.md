## Definition
Used to determine which behaviours are *interesting*/flaggable when [[Fuzzing]] a system.

For example:
- Does the [[SUT]] crash
- Is new code covered/used by the input that was not previously
- Does a dynamic analysis (e.g. a [[Compiler Sanitizers]]) report an issue
- Does an assertion fail (often causing a system crash)
- Does the [[SUT]] behave correctly / output is valid?

## Derived Test Oracles
