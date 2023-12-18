## Definition
$$L = (L, \sqsubseteq) = (L, \sqsubseteq, \sqcup, \sqcap, \bot, \top) \ where \ \begin{split} 
\bot \equiv \sqcup \emptyset \equiv \sqcap L & \ \text{(least element)} \\
\top \equiv \sqcap \emptyset \equiv \sqcup L & \ \text{(greatest element)} \\
\end{split}$$
## Examples
### [[Power Set]] Lattice
- Using $l_1 \cap l_2$ and $l_1 \cup l_2$ for $l_1 \sqcap l_2$ and $l_1 \sqcup l_2$
- For $\mathcal{P}(X)$ $\top = X$ and $\bot = \emptyset$
### Total Function Space
Given a [[Partial Order|partially ordered set]] $L_1, \sqsubseteq_1$  and a set $S$ we can define $L = (L, \sqsubseteq)$ as:
$$L = \{ f \ : \ S \to L_1 \ | \ f \text{ is a total function}\} \ \text{ (The set of total functions)}$$
$$f \sqsubseteq f' \Leftrightarrow \forall s \in S : f(s) \sqsubseteq_1 f'(s) \ \text{ (A function is less, if it always maps to less)}$$
- For example On $S = \mathbb{Z}$ , with $L$ composed of functions on integers, we can have $\lambda x. 2 * x \sqsubseteq \lambda x . 3 * x$
- We can also get $L_1$ as a complete lattice, so as $L$ makes use of $L_1$, it is also a [[Complete Lattice]] where 
   $$\bigsqcup Y = \lambda s .  \bigsqcup_1 \{f(s) \ | \ f \in Y\} \ \text{ and } \ \bot = \lambda s . \bot_1 $$   