## Definition
$$\begin{split}  \end{split}$$

## Empty Heap
$emp$ is used to denote a heap with no values mapped.
- See [[Satisfiability Relation#Dot]] for extending first order logic with empty heaps
## Cell Assertion

$$\begin{matrix*}[l l]
\vdash E_1 \mapsto E_2 & \Rightarrow E_1 \in \mathbb{N} \land E_2 \in Val \\
\vdash E_1 \mapsto E_2 \star E_3 \mapsto E_4 & \Rightarrow E_1 \neq E_3 \\
\vdash E_1 \mapsto E_2 \land E_3 \mapsto E_4 & \Rightarrow E_1 = E_3 \land E_2 = E_4 \\
\end{matrix*}$$
