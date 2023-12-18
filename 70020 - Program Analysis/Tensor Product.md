## Definition
$$\begin{bmatrix} 
a_{1,1} & \dots & a_{1,m} \\
\vdots & \ddots & \vdots \\
a_{n,1} & \dots & a_{n,m} \\
\end{bmatrix} \otimes \begin{bmatrix} 
b_{1,1} & \dots & b_{1,x} \\
\vdots & \ddots & \vdots \\
b_{y,1} & \dots & b_{y,x} \\
\end{bmatrix} = \begin{bmatrix} 
a_{1,1} \begin{bmatrix} 
b_{1,1} & \dots & b_{1,x} \\
\vdots & \ddots & \vdots \\
b_{y,1} & \dots & b_{y,x} \\
\end{bmatrix}& \dots & a_{1,m} \begin{bmatrix} 
b_{1,1} & \dots & b_{1,x} \\
\vdots & \ddots & \vdots \\
b_{y,1} & \dots & b_{y,x} \\
\end{bmatrix}\\
\vdots & \ddots & \vdots \\
a_{n,1}\begin{bmatrix} 
b_{1,1} & \dots & b_{1,x} \\
\vdots & \ddots & \vdots \\
b_{y,1} & \dots & b_{y,x} \\
\end{bmatrix} & \dots & a_{n,m} \begin{bmatrix} 
b_{1,1} & \dots & b_{1,x} \\
\vdots & \ddots & \vdots \\
b_{y,1} & \dots & b_{y,x} \\
\end{bmatrix}\\
\end{bmatrix}$$
- $\mathbf{A}_{n \times m} \otimes \mathbf{B}_{y \times x} = \mathbf{C}_{ny \times mx}$
- Can construct a base of $\mathcal{V} \otimes\mathcal{W}$ using the base vectors of $\mathcal{V}$ and $\mathcal{W}$.
- $dim(\mathcal{V} \otimes \mathcal{W}) = dim(\mathcal{V}) \times dim(\mathcal{W})$
- We can represent joint distributions on $X \times Y$ in $\mathcal{V}(x) \otimes \mathcal{V}(y)$

[[TODO]] Slide 29
