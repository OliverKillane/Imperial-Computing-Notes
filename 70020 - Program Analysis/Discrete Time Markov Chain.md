## Definition
A matrix describing the probability of transitioning from one state to another.
$$(\mathbf{T})_{ij} = \begin{cases} 
p & if \ C_i = \langle S, \sigma \rangle \Rightarrow_p C_j = \langle S', \sigma' \rangle \\
0 & otherwise \\
\end{cases} \text{ for } \mathbf{T} = \begin{bmatrix} & \dots \\
\vdots & \ddots \\\end{bmatrix}$$
With transitions implemented as:
$$\mathbf{d}_n \cdot T = \sum_i{(\mathbf{d}_n)_i \cdot \mathbf{T}_{ij}} = \mathbf{d}_{n+1}$$
$$[p_{S_1}, p_{S_2}, \dots, p_{S_n}]_{step \ n} \cdot \begin{bmatrix}

S_1 \Rightarrow_p S_1 & S_1 \Rightarrow_p S_2 & \dots & S_1 \Rightarrow_p S_n\\

S_2 \Rightarrow_p S_1 & S_2 \Rightarrow_p S_2 & \dots & S_2 \Rightarrow_p S_n \\

\vdots & \vdots & \ddots & \vdots \\

S_n \Rightarrow_p S_1 & S_n \Rightarrow_p S_2 & \dots & S_n \Rightarrow_p S_n \\

\end{bmatrix} = [p_{S_1}, p_{S_2}, \dots, p_{S_n}]_{step \ n + 1}$$
