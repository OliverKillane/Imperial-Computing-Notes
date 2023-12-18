## Definition
Given some set $\mathbf{Data}$ of [[Abstract Domains#Abstract Value|abstract values]]:
$$\widehat{v} \in \widehat{\mathbf{Val}}_d = \mathcal{P}(\mathbf{Term} \cup \mathbf{Data})$$
For each constant $c \in \mathbf{Const}$ we use an element $d_c \in \mathbf{Data}$. For each operator we use:
$$\widehat{op} : \widehat{\mathbf{Val}}_d \times \widehat{\mathbf{Val}}_d \to \widehat{\mathbf{Val}}_d \text{ typically of form } \bigcup \left\{d_{op}(d_1, d_2) \ | \ \begin{split}
d_1 \in & \widehat{v}_1 \cap \mathbf{Data} \\
d_2 \in & \widehat{v}_2 \cap \mathbf{Data}
\end{split}\right\}$$
For some function $d_{op}: \mathbf{Data} \times \mathbf{Data} \to \mathcal{P}(\mathbf{Data})$
## Examples
### Sign detection
$$\mathbf{Data}_{sign} = \{tt,ff,-,0,+\} \text{ with } d_{true} = tt \text{ and } d_{n \in \mathbb{N}} = sign(n)$$
We can also specify the $d_+$ operator with $\widehat{+}$ defined from:
$$\begin{matrix*}[l | c c c c c ] 
d_+ & tt & ff & - & 0 & + \\
\hline
tt & \emptyset & \emptyset & \emptyset & \emptyset & \emptyset &  \\
ff & \emptyset & \emptyset & \emptyset & \emptyset & \emptyset &  \\
- & \emptyset & \emptyset & \{-\} & \{-\} & \{-,0,+\} \\
0 & \emptyset & \emptyset & \{-\} & \{0\} & \{+\} \\
+ & \emptyset & \emptyset & \{-,0,+\} & \{+\} & \{+\} \\
\end{matrix*}$$
We can then analyse:
```haskell
let f = (\x -> (if x > 0 then (\y -> y) else (\z -> 25))) in (((f 3) 0))
```
$$\mathbf{let} \ \left(
\mathbf{fn} \ x \Rightarrow \left( 
\mathbf{if} \ \left( x^1 > 0^2 \right)^3 \ \mathbf{then} \ \left(\mathbf{fn} \ y \Rightarrow y^4 \right)^5 \ \mathbf{else} \ \left(\mathbf{fn} \ x \Rightarrow 25^6\right)^7
\right)^8
\right)^9 \ \mathbf{in} \ \left( \left( \left( f^{10} \ 3^{11} \right)^{12} \ 0^{13}  \right)^{14} \right)^{15}$$

[[TODO]]

