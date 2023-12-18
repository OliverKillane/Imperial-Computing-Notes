## Relations
Each is of the form $e,s,h \vDash P$ where:
- $e$ is the [[Logical Environment]]
- $s$ is the [[Variable Store]]
- $h$ is the [[Heap]]
The relation is between [[Logical States]] and [[Assertions]].
### Cases
### Logical
$$\begin{matrix*}[l l l] 
e, s, h \vDash & P_1 \land P_2 & \Longleftrightarrow e, s, h \vDash P_1 \land e, s, h, \vDash P_2 \\
e, s, h \vDash & P_1 \Rightarrow P_2 & \Longleftrightarrow e, s, h \vDash P_1 \Longrightarrow e, s, h, \vDash P_2 \\
e, s, h \vDash & True & \Longleftrightarrow e,s,h \vDash always \\
e, s, h \vDash & False & \Longleftrightarrow e,s,h \vDash never \\
e, s, h \vDash & E_1 = E_2 & \Longleftrightarrow \mathcal{E} \mathopen{\lbrack\!\lbrack} E_1  = E_2 \mathopen{\rbrack\!\rbrack}_{e,s} = true \\
e, s, h \vDash & E_1 > E_2 & \Longleftrightarrow \mathcal{E} \mathopen{\lbrack\!\lbrack} E_1  > E_2 \mathopen{\rbrack\!\rbrack}_{e,s} = true \\
e, s, h \vDash & E_1 \in X & \Longleftrightarrow \mathcal{E} \mathopen{\lbrack\!\lbrack} E \in X \mathopen{\rbrack\!\rbrack}_{e,s} = true \\
\end{matrix*}$$
For $\exists$ we need to add x into the [[Logical Environment]].
$$e,s,h \vDash \exists x . P  \Longleftrightarrow \exists v \in Val . \ e[x \to v], s, h \vDash P$$
### Separating Conjunction
The [[Separating Conjunction]] $\star$ is given as:
$$e,s,h \vDash P_1 \star P_2 \Longleftrightarrow \exists h_1, h_2 \in Heap. \ h = h_1 \uplus h_2 \land e, s, h_1 \vDash P_1 \land e, s, h_2 \vDash P_2$$
- Can split the heap into two disjoint heaps $h_1 \uplus h_2$.
- [[Partial Heaps]] $h_1$ and $h_2$ satisfy $P_1$ and $P_2$ respectively, both do not need to satisfy both
- The magic wand operator is not required for the course.
### [[Heap|Heaps]]
The [[Heap#Empty Heap|empty heap]] assertion requires no heaps.
$$e,s,h \vDash \mathbf{emp} \Longleftrightarrow h = \emptyset$$
To get the correct shape for some logical operators we can use *dot* to add the empty heap to assertions:
$$\begin{split}
E_1 \overset{.}= E_2 & \triangleq \mathbf{emp} \land E_1 = E_2 \\
E_1 \overset{.}\in E_2 & \triangleq \mathbf{emp} \land E_1 \in E_2 \\
\end{split}$$

Otherwise we can use $\mapsto$ to declare single cell on the heap.
$$e,s,h \vDash E_1 \mapsto E_2 \Longleftrightarrow h = \left\{\mathcal{E}\mathopen{\lbrack\!\lbrack}E_1\mathopen{\rbrack\!\rbrack}_{e,s} \mapsto \mathcal{E}\mathopen{\lbrack\!\lbrack}E_2\mathopen{\rbrack\!\rbrack}_{e,s}   \right\}$$
We can use *n-ary* cells by shorthand $E_a \mapsto E_1, E_2, \dots, E_n$ as:
$$(E_a \mapsto E_1) \star (E_a + 1 \mapsto E_2) \star \dots \star (E_a + (n-1) \mapsto E_n)$$
We can also use the [[Hoare Logic]] heap notation within [[Separation Logic Without Functions]] as:
$$
E_1 \hookrightarrow E_2 \triangleq E_1 \mapsto E_2 \star True
$$
### Iteration
```rust
for j in e1..e2 { P(); };
```
$$\begin{split} e,s,h \vDash \mathrlap{\bigcirc} * \ _{E_1 \leq x < E_2 }  \Longleftrightarrow \ &  \mathcal{E}\mathopen{\lbrack\!\lbrack}E_1\mathopen{\rbrack\!\rbrack}_{e,s} = i \ \land \\
& \mathcal{E}\mathopen{\lbrack\!\lbrack}E_2\mathopen{\rbrack\!\rbrack}_{e,s} = k \ \land \\
& \left( i < k \Longrightarrow \exists h_i , \dots, h_{k-1} = h_i \uplus\dots \uplus h_{k-1} \land \forall j. \ i \leq j < k \Longrightarrow e,s,h_j \vDash P[j / x] \right) \ \land \\
& (i \geq k \Longrightarrow h = \emptyset)
\end{split}$$
- Evaluate $E_1$ and $E_2$ to get bounds
- If looping $k - i$ times , split into disjoint heaps and then check $P$ using a heap, and the corresponding $j$ (iteration) value. 
### Classical Assertions
We can define $P_1 \lor P_2$, $\neg P$, $\forall x. P$ normally.
## Dot
To get the correct shape for some logical operators we can use *dot*:
$$\overset{.}{\in} \ \overset{.}{=}$$ 