## [Website](https://klee.github.io/)
## Summary
A symbolic execution tool acting on [[LLVM IR]] (meaning llvm targeting languages such as C/C++ through `clang`, or Rust through `rustc` can be analysed).

Dynamically instruments the [[LLVM IR]] as it interprets it.

```bash
clang –c –emit-llvm bpf.c # generate llvm ir
klee bpf.bc               # symbolically execute 
```
### Paths
Each path in the program is part of an execution tree. The executor manages a set of states at different parts of the tree that incrementally explore this.

| Name | Definition |
| ---- | ---- |
| Infeasable Path | Where the constraints on a symbolic value are unsatisfiable. These paths are not explored as they cannot be reached in execution. |
| Path Condition | The conjunction of constraints gathered on an execution path. |
### All-Value Checks
Can implicitly check for [[Generic Bugs]] such as issue with:
- pointer dereferencing
- array indexing
- division/modulo operations
It can also check [[Functional Bugs]] such as assert statements.

