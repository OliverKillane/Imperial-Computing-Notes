## Definition
After [[Constraint Generation]] we solve using a graph-based formulation
- $W$ is a worklist of nodes with outgoing edges to traverse.
- $D$ is a data array that gives each node an element $\widehat{\mathbf{Val}}_*$
- $E$ (edge array) gives a set of constraints for each node fr which successors can be computed.
## Constraints Graph
$$D[p] = \{t \ | \ (\{t\} \subseteq p) \in \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} e_\star \mathopen{\rbrack\!\rbrack}\}$$
Nodes $C(\ell)$ and $r(x)$

| Relation | Edges |
|-|-|
| $p_1 \subseteq p_2$ | $p_1 \to p_2$ |
| $\{t\} \subseteq p \Rightarrow p_1 \subseteq p_2$ | $p_1 \to p_2$ and $p \to p_2$ |

## Solving Algorithm
$$solve : \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} \ e_\star \ \mathopen{\rbrack\!\rbrack} \to (\ \widehat{C}, \ \widehat{\rho} \ )$$
```python
def solve(ccs: C*[[e*]]) -> tuple[CHat, RhoHat]:
	# Initialise
	W = []
	D = {}
	for q in nodes(ccs):
		D[q] = ()
		E[q] = []	

	# Add d to queue for node q
	def add(q, d):
		if d not in D[q]
			D[q] = D[q] union d
			W = [q] + W

	# Construct Graph
	for cc in ccs:
		switch cc:
			{t} <= p: 
				add(p, {t})
			p1 <= p2: 
				E[p1] = [cc] + E[p1]
			{t} <= p ==>> p1 <= p2:
				E[p1] = [cc] + E[p1]
				E[p] = [cc] + E[p]

	# Iterate
	while len(W) > 0:
		q = W[0]
		W = W[1:]
		for cc in E[q]:
			switch cc:
				p1 <= p2:
					add(p2, D[p1])
				{t} <= p ==>> p1 <= p2:
					if t in D[p]:
						add(p2, D[p1])

	# Recording
	C = CHat()
	r = RhoHat()
	for l in labels:
		C[l] = D[C[l]]
	for x in variables:
		r = D[r[x]]
	
	return C, r
```


