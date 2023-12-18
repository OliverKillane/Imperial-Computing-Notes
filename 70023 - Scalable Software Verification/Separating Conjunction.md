## Definition
As defined in the [[Satisfiability Relation#Separating Conjunction]].
- Combines disjoint heaps

## Properties
$$\begin{matrix*}[l l l ] 
\vdash P \star Q & \Leftrightarrow Q \star P & \text{(commutativity)} \\
\vdash P \star (Q \star R) & \Leftrightarrow (P \star Q) \star R & \text{(associativity)} \\
\vdash P \star emp & \Leftrightarrow P & \text{(identity)} \\
\vdash (P_1 \land P_2) \star Q & \Rightarrow (P_1 \star Q) \land (P_2 \star Q) & \text{(Distributivity of $\land$, notice $\Rightarrow$)} \\
\vdash (P_1 \lor P_2 ) \star Q & \Leftrightarrow (P_1 \star Q) \lor (P_2 \star Q) & \text{(Distributivity of $\lor$)}\\
\vdash (\exists x. P) \star Q & \Leftrightarrow \exists x. (P \star Q) & if \ x \not\in flv(Q) \ \text{ (Scope extrusion for $\exists$ over $\star$)} \\
\vdash P \star x \overset{.}= E & \Rightarrow P & \text{(Forget Equality)} \\
\vdash P \star x \overset{.}= E & \Rightarrow x = E & \text{(Keep Equality)}
\end{matrix*}$$
