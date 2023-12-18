## Definition
$$ \sqsubseteq \ : \ L \times L \rightharpoonup \{tt, \ ff\} \ \text{ or we can use } \ \sqsubseteq \ \subseteq L \times L$$
$$\sqsubseteq \text{ is } \begin{matrix*}[l l l] 
\text{reflexive} & \forall l : &  l \sqsubseteq l \\
\text{transitive} & \forall l_1, l_2, l_3 : & l_1 \sqsubseteq l_2 \land l_2 \sqsubseteq l_3 \Rightarrow l_1 \sqsubseteq l_3 \\
\text{anti-symmetric} & \forall l_2, l_2 : & l_1 \sqsubseteq l_2 \land l_2 \sqsubseteq l_1 \Rightarrow l_1 = l_2
\end{matrix*}$$
A partial ordering is a relation on the set.
- A partially ordered set $(L, \sqsubseteq)$ is a set with a partial ordering
- We can use [[Hasse Diagrams]] to represent
- Can also be considered as a [[Partial Function]]

## Upper/Lower Bounds
Given partially ordered set $(L, \sqsubseteq)$, and a subset $Y \subset L$
$$\begin{split} 
l \in L \land \forall l' \in Y : l' \sqsubseteq l \Rightarrow & l \text{ is an upper bound} \\
l \in L \land \forall l' \in Y : l \sqsubseteq l' \Rightarrow & l \text{ is a lower bound} \\
\end{split}$$
### $\sqcap$/Meet Operator
The greatest lower bound (in $L$, for $Y$) $= \sqcap Y$
- A lower bound that is larger than every other upper bound for $Y$
- $l_1 \sqcap l_2 \equiv \sqcap \{l_1, l_2\}$
### $\sqcup$/Join Operator
The least upper bound (in $L$ for $Y$) $= \sqcup Y$
- An upper bound that is smaller than every other upper bound for $Y$
- $l_1 \sqcup l_2 \equiv \sqcup \{l_1, l_2\}$

By $antisymmetry$ of $\sqsubseteq$ if $\sqcup$ or $\sqcap$ exist they are unique.
## Examples
### Integers
$\mathbb{Z}$ is ordered, as is $\mathbb{N} \subset \mathbb{Z}$.
### [[Power Set]]
Here the partial ordering is $\subseteq$ itself.
- Often displayed with [[Hasse Diagrams]].


