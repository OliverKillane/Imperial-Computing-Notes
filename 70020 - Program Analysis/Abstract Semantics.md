## Definition
$$S \vdash l_1 \rightsquigarrow l_2$$
Specifies how a set of properties about a program $S$ are changed under execution.
- Also called a *Program Analysis*
- Typically $\rightsquigarrow$ is deterministic and expressed as a function $f$ with $(S \vdash l_1 \rightsquigarrow l_2) \equiv f_S(l_1) = l_2$

## Examples
### In [[While Language for Program Analysis]]
For example given a program, we may state:
$$z := 2 \times z \vdash \mathbf{even}(z) \rightsquigarrow \mathbf{even}(z) $$
- likewise with odd, $\top$ and $\bot$
