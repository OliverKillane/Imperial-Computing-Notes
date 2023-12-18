## Definition
$$ \sqsubseteq \ : \ L \times L \to \{tt, \ ff\}$$
$$\sqsubseteq \text{ is } \begin{matrix*}[l l l] 
\text{reflexive} & \forall l : &  l \sqsubseteq l \\
\text{transitive} & \forall l_1, l_2, l_3 : & l_1 \sqsubseteq l_2 \land l_2 \sqsubseteq l_3 \Rightarrow l_1 \sqsubseteq l_3 \\
\text{anti-symmetric} & \forall l_2, l_2 : & l_1 \sqsubseteq l_2 \land l_2 \sqsubseteq l_1 \Rightarrow l_1 = l_2 \\
\text{total/strongly connected} & \forall l_1, l_2 : & l_1 \sqsubseteq l_2 \lor l_2 \sqsubseteq l_1 \\
\end{matrix*}$$
An order that can compare any set total or
- Defined by a [[Total Function]]
- Can strengthen to strict ($\sqsubset$)

> Note: We are using the notation from the course, could also have used $\leq$