## Definition
Analysis of probabilistic programs (e.g. [[Las Vegas Algorithm]] or [[Monte Carlo Algorithms]]).
## Terms
| Term | Definition | Example |
|-|-|-|
| Certainty | Determinism $\to$ Definite value | $2 \in \mathbb{N}$ |
| Possibility | Non-Determinism $\to$ Set of values | $\{2,4,6,8\} \in \mathcal{P}(\mathbb{N})$ |
| Probability | Probabilistic Non-Determinism $\to$ Distribution of values / measure | $\left(0,0, \cfrac{1}{5}, 0, \dots\right) \in \mathcal{V}({\mathbb{N}})$

We can take a finite set of states $\Omega$ to construct a [[Power Set]]:
$$\mathcal{P}(\Omega) = \{ X \ | \ X \subseteq \Omega \} \text{ ordered by } \subseteq \qquad \text{or} \qquad \mathcal{P}(\Omega)  \left\{ \chi : \Omega \to \left\{0,1\right\}\right\}$$
- Given some state, is this state present / $1$ , or not present / $0$
- This works even when $\Omega$ is uncountably infinite

## Introducing Nondeterminism
We can introduce non-determinism into programs:
- *Random Assignment* (data) $x ?= \{2,4,6\}$ 
- *Probabilistic Choice* (control flow) $\mathbf{choose} \ 0.5 : (x:= 0) \ \mathbf{or} \ 0.5 : (x := 1) \ \mathbf{ro}$
- We can do *Probabilistic Choice* with integer weights, $\mathbb{R}$ values as probabilities.
For the course we use the following:
$$\begin{matrix*}[l]
S & ::= & [\mathbf{stop}]^\ell \\
&& [\mathbf{skip}]^\ell \\
&& [x := e]^\ell \\
&& [x ?= r]^\ell \\
&& S_1 ; S_2 \\
&& \mathbf{choose}^\ell \ p_1 : S_1 \ \mathbf{or} \dots \ \mathbf{ro} \\
&& \mathbf{if} \ [b]^\ell \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 \ \mathbf{fi} \\
&& \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S \ \mathbf{od} \\ 
\end{matrix*}$$
- $p_i \in \mathbb{R}$ are constants for probability.
- $r$ is a range or set (e.g. $\{0,1,2\}$ or $[0, 100)$ )
- choose can cover many cases / $\mathbf{or}$ s.
## Evaluation
The relation now needs to include the probability of the given execution path.
$$\langle S, \sigma \rangle \Rightarrow_p \langle S', \sigma' \rangle \text{ or } \langle S, \sigma \rangle \Rightarrow_p \sigma'$$
We can use a [[Discrete Time Markov Chain]] of the program to determine the probabilistic outcomes.
- Each state is $\langle S, \sigma \rangle$
## Semantics
[[Linear Operator Semantics]] or [[Discrete Time Markov Chain]] can be used. 