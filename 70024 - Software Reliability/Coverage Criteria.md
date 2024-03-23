## Definition
Criteria used to measure the progress of a testing/fuzzing campaign.
## Black Box Coverage
Based on a specification (e.g. behaviour of a public API) without knowledge of the programs internal structure.
- Works when code is unavailable (black box)
- Can uncover unimplemented parts of the specification (e.g. postconditions on public library function incorrect)
## White Box Coverage
Based on a the code / internal knowledge (control & data flow, logic).
```C
int foo(int x, int y) {
	if (x > 0)
		printf("A");
	else
		printf("B");
	if (y < 10 || y > 20)
		printf("C")
	else
		printf("D")
}
```

| Coverage Measure               | Description                                                                               | 100% Coverage                   | Tests for Example 100% Coverage                                    |
| ------------------------------ | ----------------------------------------------------------------------------------------- | ------------------------------- | ------------------------------------------------------------------ |
| Function                       | How many/which functions are called                                                       | No unreachable functions        | Any test (1)                                                       |
| Instruction / Statement / Line | Instructions hit during execution                                                         | No unreachable code             | `(10,0)` and `(-10, 15)` to get `A,C` and `B, D`                   |
| Branch / Decision              | How many branches covered (with each side of the conditional)                             | No dead branches                | *Same as instruction coverage*                                     |
| Path Coverage                  | How many possible paths are covered (can be bounded on loops, e.g. 0, 1 or >1 iterations) | verification (full, or bounded) | `(10,0)`, `(-10, 15)`, `(10, 15)`, `(-10, 0)` (all possible paths) |
*Note: Cost increasing in descending order*
### Condition Coverage
A condition is an atomic clause in a logical predicate. Condition coverage is the number of condition outcomes exercised.
```C
if ( (x > y) || ( (x < 0) && (y > 0) ) ) // x > y, x < 0, y > 0 are atoms

// Given the tests
{.x=1, .y=0}
{.x=0, .y=1}
```

| Short Circuiting | Conditions                                                  | Coverage                                                                             |
| ---------------- | ----------------------------------------------------------- | ------------------------------------------------------------------------------------ |
| On               | $\top \lor (\bot \land \bot)$, $\bot \lor(\bot \land \top)$ | $\cfrac{5}{6}$ as $x>y$ and $y>0$ both get $\top/\bot$ and $x < 0$ gets $\bot$ only. |
| Off              | $\top \lor (\_ \land \_ )$, $\bot \lor (\bot \land \_)$     | $\cfrac{3}{6}$ as $x>y$ gets \bot/\top$ and $x < 0$ gets $\bot$                      |
### Multiple Condition Coverage
Take all possible combinations (in general $\approx 2^N$ for $N$ conditions).

| Short Circuiting | Conditions                                                                                                                                                                                                                                            | Coverage       |
| ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------- |
| On               | $\top \lor (\_ \land \_)$, $\bot \lor (\bot \land \_)$, $\bot \lor (\top \land \top)$, $\bot \lor (\top \land \bot)$                                                                                                                                  | $\cfrac{2}{4}$ |
| Off              | $\bot \lor (\bot \land \bot)$, $\bot \lor (\bot \land \top)$, $\bot \lor (\top \land \bot)$, $\bot \lor (\top \land \top)$,$\top \lor (\bot \land \bot)$, $\top \lor (\bot \land \top)$, $\top \lor (\top \land \bot)$, $\top \lor (\top \land \top)$ | $\cfrac{2}{8}$ |
### Modified Condition/Decision Coverage
Decision coverage $+$ Condition Coverage $+$ Must show each atomic condition independently influences the branch outcome.
$$\text{MC/DC  Coverage}  = \text{Percentage of conditions that meet MCDC criteria}$$
In general $n+1$ tests are required for $n$ atoms, to pairs of test cases where only one atom changes, and the result of the condition changes.

| Test | $x$ | $y$ | $x>y$  | $x < 0$ | $y > 0$ | Branch |
| ---- | --- | --- | ------ | ------- | ------- | ------ |
| T1   | 1   | 1   | $\bot$ | $\bot$  | $\top$  | $\bot$ |
| T2   | 2   | 1   | $\top$ | $\bot$  | $\top$  | $\top$ |
| T3   | -1  | 1   | $\bot$ | $\top$  | $\top$  | $\top$ |
| T4   | -1  | 0   | $\bot$ | $\top$  | $\bot$  | $\bot$ |
The test cases demonstrate that each condition does independently affect the branch outcome.
- T1 $\to$ T2 shows $x > y$ changes branch outcome
- T3 $\to$ T4 shows $y > 0$ changes branch outcome
- T1 $\to$ T3 shows $x < 0$ changes the branch outcome
### Data Flow Coverage
```C
int foo(int x /* def(x, 1) */) {
	while (X > 0) { // use(x, 1)
		x = x - 1; // def(x, 2), use(x, 2)
	}
}
```
We have the pairs:
$$\begin{split} 
P1 : & \ def_1(x) \to use_1(x) \\
P2 : & \ def_1(x) \to use_2(x) \\
P3: & \ def_2(x) \to use_1(x) \\
P4: & \ def_2(x) \to use_2(x) \\
\end{split}$$
When $x \geq 2$ we get all data flows, when $x = 1$ we only get $P1, P2, P3$, and when $x = 0$ we only get $P1$.
### Mutation-Based Coverage 
We use a [[Mutation-Based Fuzzer]] and apply small transformations to the program.
- Aim to generate a test that has different behaviour between the original and mutated programs
- Can apply many mutations, on top of mutations (Higher Order Mutants)
Mutants are *killed* when a test results in differing behaviour to the original.

| Type            | Description                                                                                        |
| --------------- | -------------------------------------------------------------------------------------------------- |
| Strongly Killed | Different program outputs                                                                          |
| Weakly Killed   | Different program states (an internal component computes a different value, but outputs unchanged) |
$$\text{Mutation Coverage} = \cfrac{\text{Killed Mutants}}{\text{Total Mutants}}$$
Mutants not killed are *surviving mutants*.

Main issues
- *Equivalent Mutants* (Syntactically different, semantically identical) to the original, can never be killed. Determining if it is identical is undecidable in the general case.
- *Indistinguishable Mutants* (equivalent mutants, but to another mutant rather than the original), as many can be killed, but are actually identical, this can inflate the mutation score above what it would be if *Indistinguishable Mutants* could be eliminated.
