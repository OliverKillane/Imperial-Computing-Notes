## Definition
Analysis of behaviour collected from running programs.
- Includes [[Fuzzing]], [[Compiler Sanitizers]] 
- [[Symbolic Execution]]
- alternative to [[Static Analysis]]

| Advantage | Description |
| ---- | ---- |
| Precise | No false positives - the behaviour observed **is** from the program's execution. |
| Scalable | Can instrument software and deploy at scale (performance is proportional to regular execution). |

| Disadvantage | Description |
| ---- | ---- |
| Whole System | Difficult to analyse small sections (e.g. methods) in isolation. Typically need to instrument/test the entire executable. |
| Environment | Requires an [[Execution Environment]] |
| Coverage Dependent | If bad code is never executed under some inputs, it's behaviour is never observed. |
## Examples
- [[Valgrind]]
- [[Compiler Sanitizers#Address Sanitizer]] 