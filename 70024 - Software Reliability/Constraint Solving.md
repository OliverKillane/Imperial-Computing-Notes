## Summary

| Aim | Why |
| ---- | ---- |
| Bit Level Modelling | System level languages allow this granularity of access, and define behaviours at this level. |
| Performance | Real programs generate many complex constraints, need to analyse these programs quickly enough to be sueful. |
[[SAT]] solvers could be used to implement this, however most applications generate constraints at a higher level than just boolean formulae (e.g. integers, integer comparison). 

Hence we use [[Satisfiability Modulo Theories]] and [[BitVectors]].
- Each block of memory is represented by an array of 8-bit [[BitVectors]] to allow constraints with bit-level accuracy.
- Operations on [[BitVectors]] include concatenation, extraction, bitwise operations and arithmetic.
- Eagre translation is used to simplify formulas at the theory level (e.g. $x - x \equiv 0$)
- Arithmetic can be encoded as a formula representing a circuit (e.g. a ripple-carry adder)
## Arrays

```rust
/// Read a value
fn read(a: &Array, i: Index) -> Value;

/// return a new array that is a copy of a, with v at index i
fn write(a: &Array, i: Index, v: Value) -> Array;
```
$$\begin{matrix*}[l r l l] 
\forall a, i, j. & i = j & \Rightarrow read(a,i) = read(a,j) & \text{Array Congruence} \\
\forall a, i, j, v. & i = j & \Rightarrow read(write(a, i, v), j) = v & \text{Read-Over-Write 1}\\
\forall a, i, j, v. & i \neq j & \Rightarrow read(write(a, i, v), j) = read(a, j) & \text{Read-Over-Write 2} \\
\end{matrix*}$$
### Eliminating Arrays
#### Eliminate Writes
$$\begin{matrix*} 
read(write(a, v, i), j) \Leftrightarrow ite(i = j, v, read(a, j))
\end{matrix*}$$
The write can be eliminated, instead just check if the $read$ reads from the index of the write, in which case just return the new value.
#### Eliminate Reads
Can replace each syntactically-unique $read$ with a fresh variable. For each array access with the same indices, we can imply the same variable is used (pairwise compare all indexes).
- Expensive as it expands formulas by $\cfrac{n(n-1)}{2}$ terms (where $n$ are the syntactically different indexes) to compare all indexes used.

For example:
$$\begin{split} 
& (a[i_1] = e_1) \land (a[i_2] = e_2) \land (a[i_3] = e_3) \land (i_1 + i_2 + i_3 = 6) \\
\to \ & (v_1 = e_1) \land (v_2 = e_2) \land (v_3 = e_3) \land (i_1 + i_2 + i_3 = 6) \\
\to \ & (i_1 = i_2 \Rightarrow v_1 = v_2) \land (i_1 = i_3 \Rightarrow v_1 = v_3) \land (i_2 = i_3 \Rightarrow v_2 = v_3)\\
\end{split}$$
### Array-Based Refinement
When we cannot eliminate the array, we can 
[[TODO]]

## Performance
[[Satisfiability Modulo Theories]] solving is NP-Complete and hence expensive, it is also invoked at every branch.
- [[70024 - Software Reliability/Constraint Solving#Eliminating Arrays|Elimination]] of constraints.
- Caching constraints and the values satisfying them.
- Constraint simplification
- Summarizing loops
### Use Different SMT/SAT Solvers
Different solvers perform differently on different formulas, so we can invoke multiple and see which is the fastest.
### Eliminating Irrelevant Constraints
Many conditions only rely on a small number of variables. We only need to include relevant constraints to a branch condition.
### Caching Solutions
Lots of similar constraint sets for branches (e.g. in loops, the same constraints used many times).
### Array Transformation
#### Index-Based
```rust
b[k] > 0
```
We can add in constraints on the indices of `b` that are in some value range.
#### Value-Based
```rust
b[k] > x
```
we can turn this into:
$$ite(0 \leq k \leq \dots, ite( k = \dots,  ite(\dots, ))) > x$$
Effectively converting the array access into a set of conditionals in an expression.