## Definition
Getting a fixed point by only updating information when necessary. Can determine which program points affect which other program points.
$$\text{Monotone Framework} \to MFP_\circ \text{ or } MFP_\bullet$$
- Takes in an instance of a [[Monotone Framework]] and outputs the [[MFP]]
- The MFP has a work list, on analysing some $\ell$ use successor/predecessor nodes (depending on [[Forward and Backward Analysis]]) to add new nodes to the work list to be updated.

```python
@dataclass
class MonotoneFramework:
	L: CompleteLattice # The lattice
	F: set[L -> L]     # The transfer functions (for nodes)
	Flow: set[(L,L)]   # The flow (or flow^R)
	E: set[L]          # Extremal labels
	iota: Val          # Extremal value
	f: set[L -> TransferFunction]


def initialise(F: flow, analysis: Analysis, MF: MonotoneFramework) -> list[(L,L)]:
	W = []
	for (l1, l2) in F:
		W = [(l1, l2)] + W
	for l in F + E:
		if l in E:
			analysis[l] = MF.iota
		else:
			analysis[l] = NotPresent

def iterate(F: flow, analysis: Analysis, W: list[L], MF: MonotoneFramework):
	while len(W) != 0:
		l1, l2 = W[0]
		W = W[1:]
		if MF.f(analysis[l1]) > MF.f(analysis[l2]):
			analysis[l2] = analysis[l2] $\cup$ MF.f(analysis[l1])
			W = [(la, lb) for (la, lb) in F if la = l2] + W

def present(F: flow, analysis: Analysis, MF: MonotoneFramework) ->  tuple[MFP, MFP]:
	for l in F + MF.E:
		MFP_\circ(l) = analysis[l]
		MFP_\bullet(l) = MF.f(analysis[l])
	return MFP_\circ, MFP_\bullet
```
## Complexity
Assume:
- $E$ and $F$ contain at most $b \geq 1$ labels
- $F$ contains $e \geq b$ pairs
- $L$ has finite height $h \geq 1$
Hence `initialise` and `present` perform at most $O(b + e)$ operations and `iterate` a pair is placed $O(h)$ times (as $\sqsubseteq$ is part of a [[Complete Lattice]] adhering to the [[Chains#Ascending/Descending Chains|ACC]]) each adding some pairs (at most $e$), we get:
$O(h \times e) + O(e + b) \Rightarrow O(h \times e)$

For [[Reaching Definitions]] we can show that it reduces complexity from $O(b^3)$ to $O(b^2)$ where $b = |\mathbf{Lab}_*|$.
## Termination
MFP always terminates due to ACC, even for a loop, we eventually stop adding nodes because we eventually get to a maximum analysis.
