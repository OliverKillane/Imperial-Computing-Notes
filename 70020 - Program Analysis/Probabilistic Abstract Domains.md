## Definition
[[Abstract Domains]] for [[Probabilistic Program Analysis]].
- *probabilistic domain* is a vector space which represents distributions $\mathbf{Dist}(\mathbf{State}) \subseteq \mathcal{V}(\mathbf{State})$
- For a finite number of states we can use 
$\mathcal{V}(\mathbf{State}) = \{(v_s)_{s \in \mathbf{State}} \ | \ v_s \in \mathbb{R}\}$
- For an infinite number of states we can use a [[Hilbert Space]] $\mathcal{V}(\mathbf{State}) = \ell^2(\mathbf{State})$
*Note: we only consider [[Normed Vector Spaces]]*

## Abstraction
We can use a [[Hilbert Space]] based concrete and abstract, and use the [[Moore-Penrose Generalised Inverse]]  as our concretisation function.
$$\mathbf{T}^\#(P) = \sum_{\langle i, p_{ij}, j \rangle \in \mathcal{F}(P)} p_{ij} \cdot \mathbf{T}^\#(\ell_i, \ell_j)$$
so by linearity we can get:
$$\mathbf{T}^\# (\ell_i, \ell_j) = (\mathbf{A}_1^\dagger \mathbf{N}_{i1}\mathbf{A}_1) \otimes (\mathbf{A}_2^\dagger \mathbf{N}_{i2}\mathbf{A}_2) \otimes \dots \otimes (\mathbf{A}_v^\dagger \mathbf{N}_{iv}\mathbf{A}_v) \otimes M_{ij}$$

## Examples
### Parity
Given $\mathcal{V}(\{1, \dots, n \})$ we can create a parity abstraction operator as:
$$\mathbf{A}_p = \begin{bmatrix} 
1 & 0 \\
0 & 1 \\
1 & 0 \\
0 & 1 \\
\vdots & \vdots \\
\end{bmatrix} \quad \text{and} \quad \mathbf{A}_p^\dagger \begin{bmatrix} 
\cfrac{2}{n} & 0 & \cfrac{2}{n} & 0 & \cdots \\
0 & \cfrac{2}{n} & 0 & \cfrac{2}{n} & \cdots \\
\end{bmatrix}$$
Hence we can now use $\langle \mathbf{A}_p \cdot c, d \rangle \approx \langle c, \mathbf{A}_p^\dagger \cdot d \rangle$ to convert back and forth with $\alpha$ and $\gamma$.


