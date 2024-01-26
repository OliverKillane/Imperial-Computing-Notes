## Definition
Using a grammar for a text input to generate valid random inputs.

Taking some grammar:
```text
Expr ::= Number | Expr Expr Op
Op   ::= '+' | '-' | '*' | '/'
Number ::= <32-bit signed integer>
```
Then randomly traversing the grammar from a start symbol:
- Randomly pick the non-terminal symbol and jump to its production rule.
- We need to consider the distribution of outputs (e.g. with integers, to bias towards edge values? To bias towards complexity rather than simple/shallow trees?) (See [[Swarm Testing]])
