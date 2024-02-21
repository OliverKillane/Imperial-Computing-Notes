## Definition
Testing a system ([[SUT]]) using input that are wholly or partially randomly-generated.

The goal is to get the interesting behaviour to aide in finding bugs.
- *interesting* is application dependent, most often it means crashing the system.
### Fuzzer Types
- [[Generation-Based Fuzzer]]s and [[Mutation-Based Fuzzer]]s as well as combinations of both.
- [[Dumb Fuzzing]] versus [[Smart Fuzzing]]
- [[Feedback-Directed Fuzzing]]
- [[Black-Box Fuzzing]] vs [[Grey-Box Fuzzing]] vs [[White-Box Fuzzing]]
## Input Types
| Input | For Compiler Fuzzing |
| ---- | ---- |
| Totally Invalid | Random invalid strings to check invalid inputs are not acceptable. |
| Malformed Inputs | Sequences of tokens structurally correct, but invalid. |
| Inputs with high validity | Token sequences that are in the language's grammar, but are ensured to be not semantically valid |
| High Integrity | Well formed programs free from undefined behaviour. |
Whenever using random inputs, it is important to consider their distribution (e.g. generating numbers, what should be distribution be like to get maximal coverage?). One way to improve this is with [[Swarm Testing]].
### Minimal Requirements
| Component | Description |
| ---- | ---- |
| [[SUT]] | The system to provide input to |
| [[Oracle]] | To determine which behaviours are *interesting* |
### Advantages
- Effective in finding edge-case inputs missed by human written test suites
- Can automatically increase coverage of a codebase
*Note: Can be used to find exploitable defects in programs. We consider it an advantage for the developer to find them first!*
## Early Days
> *_We didn't call it fuzzing back in the 1950s, but it was our standard practice to test programs by inputting decks of punch cards taken from the trash. We also used decks of random number punch cards. We weren't networked in those days, so we weren't much worried about security, but our random/trash decks often turned up undesirable behavior. Every programmer I knew (and there weren't many of us back then, so I knew a great proportion of them) used the trash-deck technique._*
>  **- [Gerald Weinberg's Secrets of Writing and Consulting: Fuzz Testing and Fuzz History (secretsofconsulting.blogspot.com)](http://secretsofconsulting.blogspot.com/2017/02/fuzz-testing-and-fuzz-history.html)

### Introduction of *Fuzzing*
In 1990 the term *fuzzing*was introduced by a paper testing linux utilities with random data.
- The paper: [An empirical study of the reliability of UNIX utilities | Communications of the ACM](https://dl.acm.org/doi/10.1145/96267.96279)
- Tested if random inputs could cause the utilities to crash.
- This was a [[Generation-Based Fuzzer|generating]] [[Dumb Fuzzing|dumb]] fuzzer
## Example
### GLFuzz
Generates OpenGL shader programs by mutation (transforms existing programs), but also can insert some  randomly generated code fragments (generation).
### [[American Fuzzy Lop (AFL)]]
### [Peach Fuzzer](https://peachtech.gitlab.io/peach-fuzzer-community/)
A [[Smart Fuzzing|smart fuzzer]] for [[Generation-Based Fuzzer|generation]] and [[Mutation-Based Fuzzer|mutation]] based fuzzing, including fuzzing access to network and files. Used mainly to find security related bugs.