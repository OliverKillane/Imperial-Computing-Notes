## Expressions
$$\begin{split} 
Val & \supseteq \mathbb{N} \cup Bool \cup \{null\} \\ 
Var & \text{ ranged by } x,y,z \text{ with special element } ret
\end{split}$$
$$E := v \ | \ x \ | \ E + E \ | \ E - E \ | \ E = E \ | \ E > E \ | \ E \land E \ | \  \neg E \ | \ \dots \ \text{ where } x \in Var \text{ and } v \in Val$$
- Can arbitrarily expand with new operators as needed
- Assignment does not occur inside expressions (e.g as in C)
- Access variables from the [[Variable Store]]
## Commands
$$\begin{matrix*}[r c c l l] 
C & ::= && x := E \\
&& | & x := [E] & \text{(Dereference \& get pointer)}\\
&& | & [E] := E & \text{(Dereference \& assign)}\\
&& | & x:= new(E) \\
&& | & dispose(E) \\
&& | & skip \\
&& | & C;C \\
&& | & if \ (E) \ C \ else \ C \\
&& | & while \ (E) \ C \\
&& | & y:= f(\overrightarrow{E}) \\
\end{matrix*}$$
- Can use function $pv : Exp \to \mathcal{P}(Var)$ to get the program variables from expressions.
## Programs
Formed from a [[Function Context]] and [[While Language for Separation Logic#Commands|Command]] $\{\gamma, C\}$
## Semantics
[[TODO]]
