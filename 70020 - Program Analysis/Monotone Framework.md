## Definition
$$(L, \mathcal{F}, F, E, \iota, f)$$
Consists of:
1. A [[Complete Lattice]] $L$ that satisfies the [[Chains#Ascending Chain Condition|Ascending Chain Condition]] (with $\bigsqcup$ as the least upper bound operator)
2. A set $\mathcal{F} : \mathcal{P}(L \to L)$ of [[Properties of Functions#Monotone/Isotone/order-Preserving|Monotone Functions]]  closed under function composition.
An instance of a [[Monotone Framework]] or [[Distributive Framework]] consist of:
- A [[Complete Lattice]] $L$ 
- the space of [[Transfer Function|transfer functions]] $\mathcal{F}$
- a finite [[While Language for Program Analysis#Flow|flow]] $F$  ($flow(S_*)$ or $flow^R(S_*)$)
- [[Extremal Labels]] $E$ 
- [[Extremal Value]] $\iota$ for the [[Extremal Labels]]
- A mapping from $\mathbf{Lab}_* \mapsto F \mapsto f \in \mathcal{F}$ (mapping from labels to flow to transfer functions)
## Classical Instances
We can define [[Available Expressions]], [[Very Busy Expression Analysis]], [[Reaching Definitions]] and [[Live Variable Analysis]] within this framework as:
$$\begin{matrix*}[ l | c | c | c | c] 
& \text{Avail Exp} & \text{Reach Defs} & \text{V-Busy Exp} & \text{Live Vars} \\
\hline
L & \mathcal{P}(\mathbf{AExp}_*) & \mathcal{P}(\mathbf{Var}_* \times \mathbf{Lab}_*) & \mathcal{P}(\mathbf{AExp}_*) & \mathcal{P}(\mathbf{Var}_*) \\
\hline 
\sqsubseteq & \supseteq & \subseteq & \supseteq & \subseteq \\
\hline
\bigsqcup & \bigcap & \bigcup & \bigcap & \bigcup \\
\hline
\bot & \mathbf{AExp}_* & \emptyset & \mathbf{AExp}_* & \emptyset \\
\hline
\iota & \emptyset & \{(x, ?) | x \in FV(S_*)\} & \emptyset & \emptyset \\
\hline
E & \{init(S_*)\} & \{init(S_*)\} & final(S_*) & final(S_*) \\
\hline
F & flow(S_*) & flow(S_*) & flow^R(S_*) & flow^R(S_*)
\end{matrix*}$$
Where all have:
$$\begin{split} 
\mathcal{F} &=  \{f : L \to L \ | \ \exists l_{kill}, l_{gen} : f(l) = (l \setminus l_{kill}) \cup l_{gen} \} \\
f_\ell(l) & = (l \setminus kill([B]^\ell)) \cup gen([B]^\ell) \ \text{ where } \ [B]^\ell \in blocks(S_*) \\
\end{split}$$
