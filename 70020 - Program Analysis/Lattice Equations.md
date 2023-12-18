## Lattice Equations
Given a system of equations of unknowns $x_1, \dots , x_n$ over a complete lattice.
$$\begin{split} 
x_1 & = f_1(x_1, \dots, x_n) \\
& \dots \\
x_n & = f_n(x_1, \dots, x_n) \\
\end{split}$$
- each $x_i$ is a node on the graph, with some equation for [[Reaching Definitions]] from neighbouring nodes + $kill_{RD}$ + $gen_{RD}$ each being an $f_i$).
- Each equation is a function $F : L^n \to L^n$ as $$F(x_1, \dots, x_n) = (f_1(x_1, \dots, x_n), \dots, f_n(x_1, \dots, x_n))$$
## Chaotic Iteration
We can iteratively solve for a [[Fixed Point]] ($gfp$ or $lfp$)

1. Start with $\bot$ or $\top$ $$x_i = x_i^0 = \bot \ \text{ or } \ x_i = x_i^0 = \top$$
2. Construct a sequence by applying $f$ until convergence/sequence stabilises (on a fixed point)  $$
\begin{matrix*}[l l l]
x_i^0 & = \bot & \text{ Initial} \\
x_i^1 & = f(x_1^0, \dots, x_n^0) \\
& \dots \\
x_i^k & = f(x_1^{k-1}, \dots, x_n^{k-1}) \\
\end{matrix*}$$
## Examples
### Basic
$$\mathcal{P}(\mathcal{X}) = \mathcal{P}(\{a,b,c,d\})$$
$$\begin{split}
S_1 & = \{a\} \cup S_4 \\
S_2 & = S_1 \cup S_3 \\
S_3 & = S_4 \cap \{b\} \\
S_4 & = S_2 \cup \{b,c\} \\ 
\end{split}$$
Starting with $\bot = \emptyset$ we get:
$$\begin{matrix*}[ c c | c | c | c | c]
& 1 & 2 & 3 & 4 & 5\\
\hline
S_1 = & \emptyset & \{a\}     & \{a,b,c\} & \{a,b,c\} & \{a,b,c\} \\
S_2 = & \emptyset & \emptyset & \{a\}     & \{a,b,c\} & \{a,b,c\} \\
S_3 = & \emptyset & \emptyset & \{b\}     & \{b\}     & \{b\}     \\
S_4 = & \emptyset & \{b,c\}   & \{b,c\}   & \{a,b,c\} & \{a,b,c\} \\
\end{matrix*}$$

Starting with $\top = \{a,b,c,d\}$ we get:
$$\begin{matrix*}[ c c | c | c ]
& 1 & 2 & 3 \\
\hline
S_1 = & \{a,b,c,d\} & \{a,b,c,d\} & \{a,b,c,d\}\\
S_2 = & \{a,b,c,d\} & \{a,b,c,d\} & \{a,b,c,d\}\\
S_3 = & \{a,b,c,d\} & \{b\} & \{b\} \\
S_4 = & \{a,b,c,d\} & \{a,b,c,d\} & \{a,b,c,d\}\\
\end{matrix*}$$
