## Definition
Used to determine which functions may be applied.

In the [[Fun Language for Program Analysis]] a variable in the context $\rho$ can be a function, so we need to consider contexts to determine control flow.

e.g. consider if we could assign programs in the [[While Language for Separation Logic]], then we could have:
```python
if b:
	p = S1
else:
	p = S2
p() # Which program is it, do we want init(S1, S2) 
```