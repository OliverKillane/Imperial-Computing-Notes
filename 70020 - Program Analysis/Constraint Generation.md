## Definition
To implement a [[0-CFA Analysis]] we generate a set of constraints for the program:
- We get $\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} e_\star \mathopen{\rbrack\!\rbrack}$ (the set of constraints and conditional constraints)
- The constraints are of the form:
  $$ lhs \subseteq rhs \text{ and } \{t\} \subseteq rhs' \Rightarrow lhs \subseteq rhs \text{ where } \quad \begin{matrix*}[l l] rhs & \text{is } C(\ell) \text{ or } r(x) \\ lhs & \text{ is } C(\ell), \ r(x) \text{ or } \{t\} \\ 
  t & \text{ is of form } \mathbf{fn} \ x \Rightarrow e_0 \end{matrix*}$$
- $C(\ell)$ maps labels to constraints $\ell \in \mathbf{Label}_*$
- $r(x)$ tracks terms where $x \in \mathbf{Var}_*$
## Rules
### For [[0-CFA Analysis#Constants]]
$$\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} c^\ell \mathopen{\rbrack\!\rbrack} = \emptyset$$
### For [[0-CFA Analysis#Terms]]
$$\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} x^\ell \mathopen{\rbrack\!\rbrack} = \{r(x) \subseteq C(\ell)\}$$
### For [[0-CFA Analysis#if-else]]
$$\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} \ \left[ \mathbf{if} \ t_0^{\ell_0} \ \mathbf{then} \ t_1^{\ell_1} \ \mathbf{else} \ t_2^{\ell_2} \right]^\ell \ \mathopen{\rbrack\!\rbrack} \ = \ \begin{split} 
& \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_0^{\ell_0} \mathopen{\rbrack\!\rbrack}\\
\cup \ & \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_1^{\ell_1} \mathopen{\rbrack\!\rbrack}\\
\cup \ & \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_2^{\ell_2} \mathopen{\rbrack\!\rbrack}\\
\cup \ & \{C(\ell_1) \subseteq C(\ell)\} \\
\cup \ & \{C(\ell_2) \subseteq C(\ell)\} \\
\end{split}$$
The child constraints and in the larger $\ell$ constraint
### For [[0-CFA Analysis#Let]]
$$\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} \ \mathbf{let} \ x = t_1^{\ell_1} \ \mathbf{in} \ t_2^{\ell_2}\  \mathopen{\rbrack\!\rbrack} = \begin{split} 
& \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_1^{\ell_1} \mathopen{\rbrack\!\rbrack} \\
\cup \ & \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_2^{\ell_2} \mathopen{\rbrack\!\rbrack} \\
\cup \ & \{C(\ell_1) \subseteq r(x)\} \\
\cup \ & \{C(\ell_2) \subseteq C(\ell)\} \\
\end{split}$$
$r(x)$ needs to contain $\ell_1$ , and then the entire $\ell$ is constrained from $\ell_2$
### For [[0-CFA Analysis#Operator]]
$$\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_1^{\ell_1}\ op \ t_2^{\ell_2}  \mathopen{\rbrack\!\rbrack} \ = \ \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_1^{\ell_1} \mathopen{\rbrack\!\rbrack} \ \cup \ \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_2^{\ell_2} \mathopen{\rbrack\!\rbrack}$$
Only need the constrains from either side, based on available operators this is not a closure.
### For [[0-CFA Analysis#Closure]]
$$\mathcal{C}_\star\mathopen{\lbrack\!\lbrack} \ \left[ \mathbf{fn} \ x \Rightarrow e_0 \right]^\ell \ \mathopen{\rbrack\!\rbrack} = \left\{ \left\{ \mathbf{fn} \ x \Rightarrow e_0  \right\} \subseteq C(\ell) \right\} \cup \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} e_0 \mathopen{\rbrack\!\rbrack}$$
## For [[0-CFA Analysis#Application]]
$$\mathcal{C}_\star \mathopen{\lbrack\!\lbrack} \ \left[t_1^{\ell_1} \ t_2^{\ell_2} \right]^\ell \ \mathopen{\rbrack\!\rbrack} \ = \ \begin{split}
& \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_1^{\ell_1} \mathopen{\rbrack\!\rbrack} \\
\cup \ & \mathcal{C}_\star\mathopen{\lbrack\!\lbrack} t_2^{\ell_2} \mathopen{\rbrack\!\rbrack} \\
\cup \ & \{\{ t \} \subseteq C(\ell_1) \Rightarrow C(\ell_2) \subseteq r(x) \ | \ t = (\mathbf{fn} \ x \Rightarrow t_0^{\ell_0}) \in \mathbf{Term}_* \} \\
\cup \ & \{ \{t\} \subseteq C(\ell_1) \Rightarrow C(\ell_0) \subseteq C(\ell) \ | \  t = (\mathbf{fn} \ x \Rightarrow t_0^{\ell_0}) \in \mathbf{Term}_* \} 
\end{split}
$$
- Get constraints from both $t_1$ and $t_2$
- For every closure, if the closure is in $\ell_1$'s constraints, then $l_2$ is the $x$ in that function.
- For every closure, if the closure is in $\ell_1$'s constraints, then the whole thing ($\ell$) is going to e its $\ell_0$, so that must be in the constraints of $\ell$.
