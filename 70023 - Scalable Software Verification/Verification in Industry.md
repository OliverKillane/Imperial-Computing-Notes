## Examples
### [ASTREE](https://www.absint.com/astree/index.htm)
A static code analyser for C/C++ (up to C++17, mixed C/C++ codebases) that proves the absence of runtime errors and invalid concurrent behaviour.
- Covers undefined behaviour, uncaught runtime errors, and hardware specifics.
- *Sound* No errors signalled $\Rightarrow$ proved absence of errors.

Satisfies the [National Institute of Standards and Technology (NIST)](https://www.nist.gov/) criteria for sound static code analysis.

Used for industrial safety-critical applications, including by Airbus, ESA & Bosch. 
### [KLEE](http://klee.github.io/)
A [[Symbolic Execution]] engine that can be used for some verification, and automatic unit test generation.
### [CBMC](http://www.cprover.org/cbmc/)
A bounded [[Model Checker]] for C/C++ (C89,99 & C++11). It is also used by [Kani](https://github.com/model-checking/kani)
(a CBMC frontend for verifying rust code).
### [Frama-C](https://frama-c.com/)
A modular C verifier.
### [Infer](https://github.com/facebook/infer)
Used by meta for bug-finding within their large codebase.
### [Gillian](https://vtss.doc.ic.ac.uk/research/gillian.html)
A model checker using its own language-agnostic intermediate representation.
- Supports verification based on [[Separation Logic Without Functions]]
- Supports both Javascript and C, exploring a Rust frontend
[[Gillian]]
### [Iris Project](https://iris-project.org/)
A framework for reasoning about concurrent programs using [[Coq]] 