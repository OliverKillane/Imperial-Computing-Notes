## Definition
Given a [[Properties of Functions#Monotone/Isotone/order-Preserving|monotone function]] $f : L \to L$ where $L$ is a [[Complete Lattice]]
$$\begin{matrix*}[l l l]
\text{Fixed Point} & Fix(f) &= \{l \ | \ f(l) = l\} \\
\text{Reductive} & Red(f) &= \{l \ | \ f(l) \sqsubseteq l \} \\
\text{Extensive} & Ext(f) &= \{l \ | \ l \sqsubseteq f(l) \} \\
\end{matrix*}$$
Given many fixed points, we can get [[Partial Order#Upper/Lower Bounds|bounds]] on the fixed points.
$$\begin{matrix*}[l l l l] 
\text{Least Fixed Point} & lfp(f) &= \sqcap Fix(f) &= \sqcap Red(f) \in Fix(f) \subseteq Red(f) \\
\text{Greatest Fixed Point} & gfp(f) &= \sqcup Fix(f) &= \sqcup Ext(f) \in Fix(f) \subseteq Ext(f) \\
\end{matrix*}$$

## Existence
> Here $n$ is the *step in the function* (I think this is analogous to iteratively solving, but not clear from the slides) 

If $L$ satisfied the [[Chains#Ascending Chain Condition|ascending chain condition]] then:
$$\exists n \in \mathbb{N} : f^n(\bot) = f^{n+1}(\bot) \ \text{ and hence } lfp(f) = f^n(\bot) $$
- Likewise with [[Chains#Ascending Chain Condition|descending chain condition]] and $gfp(f)$.
## Usage
- Consider the fixed point as the solution when iteratively solving (iterate adn get same result $\to$ am at solution)

## Knaster-Tarski Fixed Point Theorem
Let $L$ be a [[Complete Lattice]] and assume that $f :  L \mapsto L$ is an order-preserving map. Then:
$$\bigsqcup \{x \in L \ | \ x \sqsubseteq f(x)\} \in Fix(f)$$