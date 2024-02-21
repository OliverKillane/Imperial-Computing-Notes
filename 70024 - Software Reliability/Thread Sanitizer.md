## Introduction
Thread sanitizer is a [[Data Race]] detection tool that instruments C/C++ to dynamically analyse programs.

It was developed as an alternative to [[Helgrind]], after attempting improvements on [[Helgrind]] it was determined that
- [[Helgrind]] produced too many false positives
- Missed too many data races
- Too slow
## Limitations
- Linking with non-instrumented code
- static linking of libc/c++
- Position independent code not supported