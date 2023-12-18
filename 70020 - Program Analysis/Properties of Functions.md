For some function:
$$f \ : \ L_1 \to L_2$$
### Monotone/Isotone/order-Preserving
$$\forall l, l' \in L_1 : l  \sqsubseteq_1 l' \Rightarrow f(l) \sqsubseteq_2 f(l') $$
### Additive Function/Join-morphism/distributive
$$\forall l, l' \in L_1 : f(l \sqcup_1 l') = f(l) \sqcup_2 f(l')$$
### Multiplicative/Meet Morphism
$$\forall l, l' \in L_1 : f(l \sqcap_1 l') = f(l) \sqcap_2 f(l')$$
### Completely Additive/Complete Join Morphism
$$\forall Y \subseteq L_1 : \sqcup_1Y \text{ exists} \Rightarrow f(\sqcup_1 Y) = \sqcup_2\{f(l') \ | \ l' \in Y\}$$
### Completely Multiplicative/Complete Meet Morphism
$$\forall Y \subseteq L_1 : \sqcap_1Y \text{ exists} \Rightarrow f(\sqcap_1 Y) = \sqcap_2\{f(l') \ | \ l' \in Y\}$$

## Examples
### Cartesian Product
Given $L_1 = (L_1, \sqsubseteq_1)$ and $L_2 = (L_2, \sqsubseteq_2)$ we can define:
$$L = L_1 \times L_2 = \{(l_1, l_2) \ | \ l_1 \in L_1 \land l_2 \in L_2\}$$
And the partial order:
$$(l_{a1}, l_{b1})\sqsubseteq (l_{a2}, l_{b2}) \Leftrightarrow l_{a1} \sqsubseteq_1 l_{b1} \land l_{a2} \sqsubseteq_2 l_{b2}$$

We can then get a [[Complete Lattice]] for any number of cross products.

Given some $Y$:
$$\bigsqcup Y = \left( \sqcup_1\{l_1 \ | \ \exists l_2 : (l_1 , l_2) \in Y\}, \sqcup_2\{l_1 \ | \ \exists l_2 : (l_1 , l_2) \in Y\}\right)$$
- getting $(max(l_1), max(l_2))$
- Same for $\sqcap$
