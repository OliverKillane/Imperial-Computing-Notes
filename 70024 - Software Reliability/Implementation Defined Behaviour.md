## Definition
The language defines a set of allowable behaviours, the compiler must:
- Choose one option, and consistently use it everywhere
- Document this as the behaviour of the compiler
Developers can then rely on this documented compiler-defined behaviour.
## Examples
## [Arithmetic Right Shift of Negatives](https://en.cppreference.com/w/cpp/language/operator_arithmetic)
Until C++20 this was implementation defined. For example in [The GNU C Reference Manual](https://www.gnu.org/software/gnu-c-manual/gnu-c-manual.html#Bit-Shifting) specifies does arithmetic right shift on signed types.