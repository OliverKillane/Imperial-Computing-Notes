## Required Output
Depends on the requirements of the testing to be performed.

The normal considerations of fuzzing appear:
- Any input (including invalid inputs) is exhaustive, has potentially a large proportion of invalid inputs. (useful in useful for security sensitive text interfaces, less useful for finding bugs deeper that the parser in a compiler) 
- Well formed & semantically valid programs (misses all invalid programs, compilation of invalid programs)
- Grammatically correct programs (i.e. from [[Grammar-Based Fuzzing]]) 
## Generation Context
Generators can track a context of available functions, scopes and variables to generate valid inputs.
- Want to produce large programs, but that don't exceed memory/stack/cpu time limits.
- Want to cover a diverse range of language features being tested, need to weight feature use by testing priorities to achieve a *good* mix.
- Need to avoid undefined behaviour, non-termination, and avoid early termination (e.g. complex program immediately throws exception and exits).
## Equivalent By Construction Programs
Using an [[EMI-Based Fuzzer]].

## Examples
### [CSmith](https://github.com/csmith-project/csmith)
Generates C programs without [[Undefined Behaviour]] or [[Unspecified Behaviour]], on termination generated programs produces a checksum of their global variables (can compare across compilers and optimisation levels).

[[Undefined Behaviour]] is avoided by generation time mechanisms (check variable initialisation, check accesses are in bounds, check loop bounds), and runtime checks (check for zero division in *safe math* macros).

There is no guarantee of termination, timeouts can be used to avoid this problem, though this limits the execution time of programs.
#### [[Swarm Testing]]
Testing with different Csmith configurations (specify the weighting of different constructs).
- Found 104 bugs versus 73 with the default configuration
#### Evaluation
Useful for testing crash bugs, but less so for miscompilations:
- Exposes the differences between compilers
- Miscomplications produced by large programs are difficult to debug, difficult to reduce test case to one useful for a compiler developer.
- [[Test Case Reduction]] is required
### CSmithEdge
By being less conservative about [[Undefined Behaviour]] (and language semantics in general) than Csmith more bugs can be found.
- Removing runtime checks for maths.
- Generating expressions that could contain [[Undefined Behaviour]]
The weakened constraints are weighted (e.g. allow null ptr dereference in $\approx10\%$ of generated programs).

A violation of a short circuiting rule for modulus/ `%`  was found, that required the removal of safe wrappers which included bracketing that dissuaded the compiler from optimising incorrectly.

