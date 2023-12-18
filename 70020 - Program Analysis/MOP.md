## Definition
By constructing a sequences of labels (a path).
$$\overrightarrow{\ell} = [\ell_1, \dots, \ell_n]$$
Given by
$$\begin{matrix*}[l l l] 
path_\circ(\ell) & = \{[\ell_1, \dots, \ell_{n-1}] & \ | \ n \geq 1 \land \forall i < n : (\ell_i, \ell_{i+1}) \in F \land \ell_n = \ell \land \ell_1 \in E\} \\
path_\bullet(\ell) & = \{[\ell_1, \dots, \ell_{n}] & \ | \ n \geq 1 \land \forall i < n : (\ell_i, \ell_{i+1}) \in F \land \ell_n = \ell \land \ell_1 \in E\} \\
\end{matrix*}$$
- $path_\bullet(\ell)$ is up to (and including) $\ell$
- $\ell_i$ is not implying the number for your labels, just that we do not loop / go back to out final.
We can then define a transfer function over $\overrightarrow{\ell}$ as:
$$f_{\overrightarrow{\ell}} = f_{\ell_n} \circ \dots \circ f_{\ell_1} \circ id$$
- $id$ is included for the empty path $f_{[ \ ]} = id$ 
We can then get the MOP solutions by:
$$\begin{split} 
MOP_\circ(\ell) & = \bigsqcup\{f_{\overrightarrow{\ell}} \ (\iota) \ | \   \overrightarrow{\ell} \in path_\circ(\ell) \} \\
MOP_\bullet(\ell) & = \bigsqcup\{f_{\overrightarrow{\ell}} \ (\iota) \ | \   \overrightarrow{\ell} \in path_\bullet (\ell) \} \\
\end{split}$$

## Termination
Not guaranteed, MOP solution is undecidable.
## Comparison with [[MFP]]
Given some instance of a monotone framework $(L, \mathcal{F}, F, B, \iota, f)$
$$MFP_\circ \sqsupseteq MOP_\circ \land MFP_\bullet \sqsupseteq MOP_\bullet$$
If the framework is a [[Distributive Framework]] and $\forall \ell \in E \cup F. \ path_\circ(\ell) = \emptyset$ we have
$$MFP_\circ = MOP_\circ \land MFP_\bullet = MOP_\bullet$$