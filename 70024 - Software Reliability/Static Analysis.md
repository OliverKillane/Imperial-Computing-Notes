## Definition
Reasoning about behaviour of programs without executing them.
### Advantages
| Advantage | Description |
| ---- | ---- |
| High Coverage | Unlike [[Dynamic Analysis]] many static techniques do not rely on the coverage of inputs, can potentially prove about behaviour under all possible inputs. |
| Incomplete Systems | Can be applied to parts of systems (e.g. analysing an individual function), so can be used before a system is complete. |
| Scalability? | can be if applied modularly (e.g. [[Separation Logic With Functions]]) |
### Disadvantages
| Disadvantage | Description |
| ---- | ---- |
| Expensive | Can be precise, but very expensive |
| Precision | Can be made cheaper by weakening analysis (e.g. [[Abstract Interpretation]]), but at the cost of precision. |
## Examples
### Coverity ([[A Few Billion Lines of Code Later]])
### Theory of [[Program Analysis]]
