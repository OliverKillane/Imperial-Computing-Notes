## Definition
$$\langle \ell_1, p, \ell_2 \rangle $$
Flow that includes a probability.
$$
\begin{matrix*}[l c l]
flow ( & [skip]^\ell& ) = & \emptyset \\
flow ( & [stop]^\ell & ) = & \{\langle \ell, 1, \ell \rangle\} \\
flow ( & [x:=e]^\ell & ) = & \emptyset \\
flow ( & [x? = e]^\ell & ) = & \emptyset \\
flow ( & S_1;S_2 & ) = & flow(S_1) \cup flow(S_2) \cup \{\langle\ell, 1, init(S_2)\rangle \ | \ \ell \in final(S_1)\} \\
flow ( & \mathbf{choose}^\ell \ p_1 : S_2 \ \mathbf{or} \ p_2 : S_2 & ) = & flow(S_1) \cup flow(S_2) \cup \{ \langle \ell, p_1, init(S_1) \rangle, \ \langle \ell, p_2, init(S_2) \rangle \} \\
flow ( &\mathbf{if} \ [b]^\ell \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 & ) = & flow(S_1) \cup flow(S_2) \cup \{\langle \ell, 1, init(S_1) \rangle, \ \langle \ell, 1, init(S_2) \rangle\} \\
flow ( & \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S& ) = & flow(S) \cup \{\langle \ell, 1, init(S) \rangle\}\cup \{\langle \ell', 1, \ell \rangle \ | \ \ell' \in final(S)\}\\
\end{matrix*}
$$
Notice that for $\mathbf{if}$ and $\mathbf{while}$ the flow probability is $1$. Hence this probability is best interpreted as *probability if the entire state was known*.
