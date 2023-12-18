## Definition
Using a [[Discrete Time Markov Chain]] to model a [[Probabilistic Program Analysis]] is not composable (cannot split and analyse parts of the program separately).

Instead we can compose operators expression program operations.
## Configuration Space
Given a program $S$ we can identify configurations with elements in:
$$\mathbf{Dist}(\mathbf{State} \times \mathbf{Lab}) \subseteq \mathcal{V}(\mathbf{State} \times \mathbf{Lab})$$
- We have some distribution of $(\sigma, \ell)$ which is part of the set of all such pairs $\mathcal{V}$ (see [[Probabilistic Program Analysis#Terms]]).

We assume $v = |\mathbf{Var}|$ is finite, and have: $$\mathbf{State} = (\mathbb{Z} + \mathbf{B})^v = \mathbf{Value}_1 \times \mathbf{Value}_2 \times \dots \times \mathbf{Value}_v$$
- Each $\mathbf{Value}_i$ is for variable $i$, which is either an integer ($\in \mathbb{Z}$) or a Boolean.
- As states are now just tuples of variable assignments, we can combine states.
Hence we can now represent the configuration space as:
$$
\begin{split} 
& \mathbf{Dist}(\mathbf{Value}_1 \times \mathbf{Value}_2 \times \dots \times \mathbf{Value}_v \times \mathbf{Lab}) \\ 
\subseteq \ & \mathcal{V}(\mathbf{Value}_1 \times \mathbf{Value}_2 \times \dots \times \mathbf{Value}_v \times \mathbf{Lab}) \\
= \ & \mathcal{V}(\mathbf{Value}_1) \otimes \mathcal{V}(\mathbf{Value}_2) \otimes \dots \otimes \mathcal{V}(\mathbf{Value}_v) \otimes \mathcal{V}(\mathbf{Lab}) \\
\end{split}$$
- $\otimes$ is the [[Tensor Product]]

## Operations
### Update
Create a matrix of $\text{old value} \mapsto \text{new value}$ 
$$U(var \leftarrow val) = \begin{bmatrix} 
\dots & 0 & 1_{val}& 0  & \dots \\
\dots & 0 & 1_{val}& 0  & \dots \\
& \vdots & \vdots & \vdots \\
\end{bmatrix} \otimes \mathbf{I}$$
### Filter
$$P(predicate) =  \begin{bmatrix} 
p(val_1)  &       0 & 0 & \dots \\
       0 & p(val_2) & 0 & \dots \\   
0 & 0 & p(val_3) & \dots \\
\vdots & \vdots & \vdots & \ddots \\
\end{bmatrix} \otimes \mathbf{I}$$
- $P(\neg cond) = P(cond)^\bot = \mathbf{I} - P(cond)$
### Edge
$$E(\ell_1, \ell_2) = $$
## Combining
$U, E, P$ combine and sum and the [[Probabilistic Flow]] 
$$\mathbf{T}(S) = \sum_{\langle i, p_{ij}, j \rangle \in flow(S)} p_{ij} \cdot \mathbf{T}(\langle \ell_i, p_{ij}, \ell_j \rangle) \ \text{where} \ \mathbf{T}(\langle \ell_i, p_{ij}, \ell_j \rangle) = \mathbf{N}_{\ell_i} \otimes \mathbf{E}(\ell_i, \ell_j)$$
$\mathbf{N}_{\ell_i}$ is the operator for the state update (change in variable values), we can use the following transfers.
## Examples
### Basic $\mathbf{if}$
```python
if x == 0:
	x = 0
else:
	x = 1
```
$$
\begin{matrix*}[l]
\mathbf{if} \ [x == 0]^1 \ \mathbf{then} \\
\qquad [x \leftarrow 0]^2 \\
\mathbf{else} \\
\qquad [x \leftarrow 1]^3 \\
\mathbf{end} \ \mathbf{if} \\
[\mathbf{stop}]^4 \\
\end{matrix*}
$$
$$\begin{matrix*}[l] 
\mathbf{T}(S) & = & P(x = 0) \otimes E(1,2) \\
& + & P(x \neq 0) \otimes E(1,2) \\
& + & \mathbf{U} (x \leftarrow 0) \otimes E(1,3) \\
& + & \mathbf{U} (x \leftarrow 1) \otimes E(3,4) \\
& + & \mathbf{I} \otimes E(4,4) \\
\end{matrix*}$$
