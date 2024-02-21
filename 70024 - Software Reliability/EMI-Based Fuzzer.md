## Definition
Equivalence Modulo Input Fuzzers & testing is a type of [[Metamorphic Testing]] that involves generating a program that given some input $I$ covers $Cov_I$ code.

By modifying code that is not covered validly (still compiles) we can compare the behaviour of equivalent programs.

1. Get a program.
2. Get an input, $I$ get coverage $Cov_I$
3. Mutate lines that $\not\in  Cov_I$ , this is dead code, so should make no difference.
4. Test outputs of mutated programs are identical.

This is a mix of a [[Mutation-Based Fuzzer]], [[Smart Fuzzing]], and [[Black-Box Fuzzing]] (as the SUT is the compiler with unknown internals, we can still have knowledge about the language)