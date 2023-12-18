  ## Definition
Determines for each program point if a variable has a constant value on every entry to that point.
- Can be used to build [[Constant Folding]]
- It is not a [[Distributive Framework]]

$$\widehat{\mathbf{State}_{CP}} = ((\mathbf{Var_*} \to \mathbb{Z}^T)_\bot, \sqsubseteq, \sqcap, \sqcup, \bot, \lambda x . \top) \ \text{ where } \ \mathbb{Z}^T = \mathbb{Z} \cup \{\top\}$$
The [[Partial Order]] is such that $\top$ (unknown) is the $\sqcup$/max and only :
$$\forall z_1, z_2 \in \mathbb{Z} : (z_1 \sqsubseteq z_2) \Leftrightarrow (z_1 = z_2 \lor z_2 = \top)$$
We could also consider [[Complete Lattice]] $\mathbb{Z}^\top_\bot$ (with all larger than $\bot$) however we instead use $\bot$ to represent a lack of information.
$$\widehat{\sigma} \in (\mathbf{Var}_* \to \mathbb{Z}^\top)_\bot \ \text{ where } \ \widehat{\sigma}(x) = \begin{cases} 
z \in \mathbb{Z} & \text{ if variable } x \text{ is constant and equals } z \\
\top & \text{ if variable } x \text{ is not constant here} \\
\bot & \text{ if variable } x \text{'s constantness is unknown} \\
\end{cases}$$

We also have a [[Partial Order]] on $\widehat{\mathbf{State}_{CP}}$ defined as:
$$\begin{split}
\forall \widehat{\sigma} \in (\mathbf{Var}_* \to \mathbb{Z}^\top)_\bot & : \bot \sqsubseteq \widehat{\sigma} \\
\forall \widehat{\sigma_1}, \widehat{\sigma_2} \in (\mathbf{Var}_* \to \mathbb{Z}^\top)_\bot & : \widehat{\sigma_1}\sqsubseteq \widehat{\sigma_2} \Leftrightarrow \forall x : \widehat{\sigma_1}(x) \sqsubseteq \widehat{\sigma_2}(x) \\
\end{split}$$
- $\bot$ (unknown) is less than everything
- Functions are ordered larger only if they're larger for everything
Hence we can get the [[Partial Order#Upper/Lower Bounds|Least Upper Bound]] as:
$$\begin{split}
\forall \widehat{\sigma} \in (\mathbf{Var}_* \to \mathbb{Z}^\top)_\bot & : \widehat{\sigma} \sqcup \bot = \widehat{\sigma} = \bot \sqcup \widehat{\sigma} \\
\forall \widehat{\sigma_1}, \widehat{\sigma_2} \in (\mathbf{Var}_* \to \mathbb{Z}^\top)_\bot & : \forall x : (\widehat{\sigma_1} \sqcup \widehat{\sigma_2})(x) = \widehat{\sigma_1}(x) \sqcup \widehat{\sigma_2}(x) \\
\end{split}$$
## State Evaluation
$$\mathcal{A}_{CP} : \mathbf{AExp} \to (\widehat{\mathbf{State}_{CP}} \to \mathbb{Z}_\bot^\top)$$
$$\begin{matrix*}[l c r l] 
\mathcal{A}_{CP} \mathopen{\lbrack\!\lbrack} & x & \mathopen{\rbrack\!\rbrack} \widehat{\sigma} = & \begin{cases} \bot & if \ \widehat{\sigma} = \bot \\ \widehat{\sigma}(x) & otherwise \end{cases} \\
\mathcal{A}_{CP} \mathopen{\lbrack\!\lbrack} & n & \mathopen{\rbrack\!\rbrack}\widehat{\sigma} = & \begin{cases} \bot & if \ \widehat{\sigma} = \bot \\ n & otherwise \end{cases} \\
\mathcal{A}_{CP} \mathopen{\lbrack\!\lbrack} & a_1 \ op_a \ a_2 & \mathopen{\rbrack\!\rbrack}\widehat{\sigma} = & \mathcal{A}_{CP}\mathopen{\lbrack\!\lbrack} a_1 \mathopen{\rbrack\!\rbrack}\widehat{\sigma} \ \widehat{op_a} \ \mathcal{A}_{CP}\mathopen{\lbrack\!\lbrack} a_2 \mathopen{\rbrack\!\rbrack}\widehat{\sigma} \\
\end{matrix*}$$

where, $\widehat{op_a}$ applies a corresponding operation to $op_a$, with the following cases.
$$r_1 \ \widehat{op_a} \ r_2 = \begin{cases} 
z_1 \ op_a \ z_2 & if \ z_1 \in \mathbb{Z} \land z_2 \in \mathbb{Z} \\
\top & if \ z_1 = \top \lor z_2 = \top \\
\bot & otherwise \text{ (at least one side unknown)} \\
\end{cases}$$
## [[Transfer Function]]
Takes a [[Properties of Functions#Monotone/Isotone/order-Preserving|monotone function]], adds new constants & non-constants and continues.
$$\mathcal{F}_{CP} = \{f \ | \ f \text{ is a monotone function on } \widehat{\mathbf{State}_{CP}}\}$$
$$\begin{matrix*}[l c r l] 
[ & x := a & ]^\ell : f^{CP}_\ell(\widehat{\sigma}) = & \begin{cases} \bot & if \ \widehat{\sigma} = \bot \\ \widehat{\sigma}[x \mapsto \mathcal{A}_{CP}\mathopen{\lbrack\!\lbrack}a\mathopen{\rbrack\!\rbrack}\widehat{\sigma}] & otherwise \end{cases} \\
[ & \mathbf{skip} & ]^\ell : f^{CP}_\ell(\widehat{\sigma}) = & \widehat{\sigma} \\
[ & b & ]^\ell : f^{CP}_\ell(\widehat{\sigma}) = & \widehat{\sigma} \\
\end{matrix*}$$
It is not a [[Distributive Framework]] by counterexample:
$$\text{For } [y := x \times x]^\ell \ \text{ where } \ \widehat{\sigma_1}(x) = 1 \text{ and } \widehat{\sigma_2} = -1$$
With $\widehat{\sigma_1}$ and $\widehat{\sigma_2}$  independently we get $y \mapsto 1$ for both. However together we would get $x \mapsto \top$ and hence $y \mapsto \top$.
$$f_\ell^{CP}(\widehat{\sigma_1} \sqcup \widehat{\sigma_2}) \text{ has } y \mapsto \top$$
$$f_\ell^{CP}(\widehat{\sigma_1}) \sqcup f_\ell^{CP}(\widehat{\sigma_2}) \text{ has } y \mapsto 1$$

