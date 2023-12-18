## Definition
$$\forall l_1, l_2 \in Y : (l_1 \sqsubseteq l_2) \lor (l_2 \sqsubseteq l_2)$$
A chain is a series of ordered elements in a partially ordered set.
- A totally [[Total Order|ordered subset]] of $L$.
- *finite chain* if
$$\{a,b,c,d,e\} \text{ and some finite chain } \{a,c,e\}$$
- The *height* of the chain is $length - 1$
### Ascending/Descending Chains
Given a sequence $(l_n)_n = (l_n)_{n \in \mathbb{N}}$ of elements in $L$:
$$n \leq m \Rightarrow l_n \sqsubseteq l_m \ \text{ (Ascending Chain)}$$
(and likewise for descending)
### Stabilising Chains
$$(l_n)_n \text{ eventally stabilises } \exists \ n_0 \in \mathbb{N} : n \geq n_0 \ \Rightarrow l_n = l_{n_0}$$
- Eventually converges on a value as $n$ increases
- Can use $\sqcap$ and $\sqcup$ on a sequence
### Ascending Chain Condition
For a partially ordered set $L = (L, \sqsubseteq)$ 
- $\text{Finite Height} \Leftrightarrow \text{All Chains are Finite}$
- $\text{Finite Height at most } h \Leftrightarrow \text{All chains contain at most } h + 1 \text{ elements}$
- $\text{Finite Height } h \Leftrightarrow \text{There exists a chain containing } h + 1 \text{ elements}$
A partially ordered set satisfied [[Chains#Ascending Chain Condition|ascending chain condition]]  iff all ascending chains eventually stabilise.
- Likewise for the [[Chains#Ascending Chain Condition|descending chain condition]]
## Examples
### With $\mathbb{N}$
We satisfy the descending chain condition as all eventually go to $\sqcap\mathbb{N} = 0$