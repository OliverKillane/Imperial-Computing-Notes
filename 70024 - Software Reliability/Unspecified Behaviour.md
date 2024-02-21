## Definition
The language defines a set of allowable behaviours for which compiler can choose any behaviour at each occurrence.

This differs from [[Implementation Defined Behaviour]] as there is no requirement for consistency. The compiler can choose any behaviour, potentially different for every occurrence in a program. 
## Examples
### [C++ Evaluation Order](https://en.cppreference.com/w/cpp/language/eval_order)
Unspecified meaning every function, aggregate constructor,  etc. can be decided differently, but it is not [[Undefined Behaviour]].