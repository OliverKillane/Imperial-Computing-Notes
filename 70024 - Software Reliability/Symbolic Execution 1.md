## Definition
By running a program on symbolic input (representing any value, can be logically constrained), every path through a program is analysed by constraining symbolic values to symbols representing the sets of possible values on the paths.
- Program instructions act on symbolic values.
- At conditionals, fork the symbolic values and constrain by the branch condition.
- On termination generate a test case by solving the constraints on the path.
### Advantages
| Advantage | Description |
| ---- | ---- |
| Automatic | Requires no input test cases, initial seeds, configuration (like [[Fuzzing]]/[[Swarm Testing]]). |
| Systematic | Can reach all possible paths in the program, and reason about all possible values on these paths. |
| Deep Bugs | Cam reason about all values, hence including extremely rare edge case values & memory layouts. |
| [[Functional Bugs]] | Can reason about logical statements given appropriate oracles. e.g. checking for crashes, given assert statements cause crashes. |
| Test Cases | Generates test cases for developers to allow them to reproduce and debug. |
### Disadvantages
| Disadvantage | Description |
| ---- | ---- |
| Complex Toolchain | Requires the source to be available, and compiled to some form the symbolic execution tool can interpret. |
| Constrain Solving | Constraint solving is expensive. |
## Mixed Concrete & Symbolic Execution
Many values are concrete (e.g. constants in the code, or concrete inputs set by the user).
- Only operations that include symbolic values need to be symbolically executed, the rest can be executed as normal.
- Allows interaction with outside environment, (e.g. operating system, un-instrumented libraries, etc.)
## Challenges
### [[Path Explosion]]
## Examples
KLEE, CREST, SPF, FuzzBall
### [[KLEE]]
### [[EXE]]
