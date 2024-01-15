## Definition
> *Something bad does not happen*

Properties that can be expressed with assertions and program instrumentation.

| Generic Bug | Instrumented By |
| ---- | ---- |
| No Null Dereferences | For all `*p` convert to `if p {*p} else { ..catch.. }` |
| No out of bounds access | Associate buffers accesses with some information on size/ranges and check before access. |
| No division by zero | Check before division/modulo |
| Constructors/Destructors Order | Can instrument variables and track order of associated method calls. |

