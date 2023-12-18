## Definition
We need to ensure correctness in program analysis.
- custom implementation for each property (e.g [[Live Variable Analysis]]) is tedious
- Abstract Interpretation is such a framework.
- Simplify concrete semantics to get an abstract interpretation / optimal approximation.

[[Abstract Interpretation]] allows us to:
- construct simplified & computable abstract semantics
- construct approximate solutions
- get the correctness of approximate solutions
## Approximations
$$\begin{split} \text{Safe Approximation:} \ & s^* \sqsubseteq s \text{ or } s \sqsubseteq s^* \\ \text{Close Approximation:} \ & \|s - s^* \| = \min_x\|s - x\| \end{split}$$
- In theoretic data structures we want safe approximations
- For [[Vector Spaces]] we want close approximations.
We can use a [[Galois Connection]]
![[abstract interpretation.drawio.svg]]
## General Construction
![[abstract interpretation general construction.drawio.svg]]
## Uniqueness & Duality
Given abstraction $\alpha$ we can derive the unique concretisation $\gamma$ by:
$$\text{Given Galois Connection } (\mathcal{C}, \alpha, \gamma, \mathcal{D}) \text{ we can define}$$
$$\alpha \text{ uniquely determines } \gamma \text{ as: } \gamma(d) = \bigsqcup \{c \ | \ \alpha(c) \leq_{\mathcal{D}} d\}$$
Each $\gamma (d)$ is the maximum of $c$ that create $\leq_{\mathcal{D}}$ d
$$\gamma \text{ uniquely determines } \alpha \text{ as: } \alpha(c) = \sqcap \{d \ | \ \gamma(d) \geq_{\mathcal{C}} c\}$$
Each $\alpha (c)$ is the minimum $d$ that creates $\geq_{\mathcal{C}}$ d

Furthermore:
- $\alpha$ is [[Completely Additive]] 
- $\gamma$ is [[Completely Multiplicative]]
- $\alpha(\bot) = \bot$
- $\gamma(\top) = \top$
## Correctness & Optimality
We can lift from some $\mathcal{D}$ into $\mathbb{Z}$ and with a [[Galois Connection]] with $\mathbb{Z}$ and some [[Property Lattice]] then apply operations.
$$\begin{matrix*}[l] 
\alpha : & \mathcal{P}(\mathbb{Z}) \to \mathcal{D} \\
\gamma : & \mathcal{D} \to \mathcal{P}(\mathbb{Z}) \\
op : & \mathbb{Z} \to \mathbb{Z} \\
\widehat{op} : & \mathcal{P}(\mathbb{Z}) \to \mathcal{P}(\mathbb{Z}) & \text{ where } \widehat{op}(X) & \triangleq \{op(x) \ | \ x \in X\}\\
op^{\#} : & \mathcal{D} \to \mathcal{D} & \text{ where } op^{\#} & \triangleq \alpha \circ \widehat{op} \circ \gamma \\
\end{matrix*}$$
- $op^{\#}$ is the most precise function on $\mathcal{D}$ satisfying:
$$\forall z \in \mathbb{Z} : \alpha(\widehat{op}(z)) \sqsubseteq op^{\#}(\alpha(z))$$
## Semantics
[[Concrete Semantics]] (at execution) and reasoned about through [[Abstract Semantics]] with a [[Correctness Relation]] $\textcolor{red}{\triangleright}$ used.
## Examples
### Cast-out-of-nines
A plausibility check for arithmetic, which just does all arithmetic modulo $9$.
- Holds as $\times, \div, +, -$ are true under modulus.
- More conservative, so failures are not real / false positive for error.
### Abstract Multiplication
To reason about multiplication, we can go from $\mathbb{Z}$ to the abstract domain of $\{\top, \mathbf{even}, \mathbf{odd}, \bot\}$, we could also represent this as a powerset $\mathcal{P}(\{\mathbf{even}, \mathbf{odd}\})$ 
$$\begin{matrix*}[| c | c c c c |]
\hline
\times^\# & \bot & \mathbf{even} & \mathbf{odd} & \top \\
\hline
\bot & \bot &\bot &\bot &\bot & \\
\mathbf{even} & \bot & \mathbf{even} & \mathbf{even} & \mathbf{even} \\
\mathbf{odd} & \bot & \mathbf{even} & \mathbf{odd} & \top \\
\mathbf{top} & \bot & \mathbf{even} & \top & \top \\
\hline
\end{matrix*}$$
Hence we have [[Galois Connection]] $(\mathcal{P}(\mathbb{Z}), \alpha, \gamma, \{\top, \mathbf{even}, \mathbf{odd}, \bot\})$ where:
$$\alpha(c) = \begin{cases} 
\bot & if \ c = \bot \\
\mathbf{even} & \text{iff} \ \forall x \in c : \exists k \in \mathbb{Z} : x = 2k \\
\mathbf{odd} & \text{iff} \ \forall x \in c : \exists k \in \mathbb{Z} : x = 2k +  1\\
\top & \text{iff} \ c = \top \\
\end{cases}$$
$$\gamma(d) = \begin{cases} 
\emptyset & \text{iff} \ d = \bot \\
E & \text{iff} \ d = \mathbf{even} \\
O & \text{iff} \ d = \mathbf{odd} \\
\mathbb{Z} & \text{iff} \ d = \top \\
\end{cases} \quad \text{where} \quad  \begin{split} 
E & = \{x \in \mathbb{Z} \ | \ \exists k \in \mathbb{Z} : x = 2k\} \\
O & = \{x \in \mathbb{Z} \ | \ \exists k \in \mathbb{Z} : x = 2k + 1\}
\end{split}$$
We need to lift multiplication to work with our sets of possible $\mathbb{Z}$s by:
$$\times : \mathbb{Z} \times \mathbb{Z} \to \mathbb{Z} \qquad \widehat{\times} : \mathcal{P}(\mathbb{Z}) \times \mathcal{P}(\mathbb{Z}) \to \mathcal{P}(\mathbb{Z}) \qquad \text{ where } X \widehat{\times} Y \triangleq \{x \times y \ | \ x \in X \land y \in Y\}$$

