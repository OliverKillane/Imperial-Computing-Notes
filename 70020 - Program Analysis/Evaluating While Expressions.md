
## Evaluation
We use a transition relation $\Rightarrow$ to map:
$$\underbrace{\langle S, s \rangle \Rightarrow s'}_{\text{Instructions and state to final state}} \qquad \underbrace{\langle S, s, \rangle \Rightarrow \langle S',s' \rangle}_{\text{Instructions and state to new instructions and state}}$$
- Can reason about execution: e.g For example proving that the solution for a live variable analysis remains a solution under program execution.
### Correctness Relation
Given some set of *live variables* $V$:
$$s_1 \sim_V s_2 \Leftrightarrow \forall x \in V : s_1(x) = s_2(x)$$
For all live variables, $s_1$ and $s_2$ agree.

For example $[x := y + z]^\ell$ with $V_1 = \{y, z\}$ and $V_2 = \{x\}$ 
- $s_1 \sim_{V_1} s_2 \Rightarrow s_1(y) = s_2(y) \land s_1(z) = s_2(z)$ 
- $s_1 \sim_{V_2} s_2 \Rightarrow s_1(x) = s_2(x)$
## Correctness Lemmas
### Lemma 1
$$\begin{matrix*}[l] 
\mathbf{if} \ \langle S, s\rangle \Rightarrow s' & \text{ then } & final(S) = \{init(S)\} \\
\\
\mathbf{if} \ \langle S, s\rangle \Rightarrow \langle S', s'\rangle & \text{ then } & final(S) \supseteq final(S') \\
&& flow(S) \supseteq flow(S') \\
&&blocks(S) \supseteq blocks(S') \\
&& S \text{ is Label Consistent} \Rightarrow S' \text{ is Label Consistent} \\
\end{matrix*}$$
### Lemma 2
$$\left(S_1 \text{ is label consistent } \land live \vDash LV^\subseteq(S_1) \land flow(S_1) \supseteq flow(S_2) \land blocks(S_1) \supseteq blocks(S_2)\right) \Rightarrow \left( live \vDash LV^\subseteq (S_2) \land S_2 \text{ is label consistent}\right)$$
### Lemma 3
$$\left( S \text{ is label consistent } \land live \vDash LV^\subseteq (S) \land (\langle S, s \rangle \Rightarrow \langle S', s' \rangle) \right) \Rightarrow live \vDash LV^\subseteq (S')$$
### Lemma 4
$$(live \vDash LV^\subseteq (S)) \Rightarrow \left(\forall (\ell, \ell') \in flow(S). \ live_{exit}(\ell) \supseteq live_{entry}(\ell')\right)$$
### Lemma 5
$$\left( S \text{ is label consistent } \land live \vDash LV^\subseteq (S) \right) \Rightarrow \left( \forall (\ell, \ell') \in flow(S) : s_1 \sim_{live_{exit}(\ell)} s_2 \Rightarrow s_1 \sim_{live_{entry}(\ell')} s_2 \right)$$
### Theorem 2
$$\left( live \vDash LV^\subseteq(S) \right) \Rightarrow \begin{cases} 
\exists s'_2 : \langle S, s_2 \rangle \Rightarrow \langle S', s'_2 \rangle \land s'_1 \sim_{live_{entry}(init(S'))} s'_2 & \mathbf{if } \ \langle S, s_1 \rangle \Rightarrow \langle S', s'_1 \rangle \land s_1 \sim_{live_{entry}(init(S))} s_2\\
\exists s'_2 : \langle S, s_2 \rangle \Rightarrow s_2' \land s_1' \sim_{live_{exit}(init(S))} s_2'& \mathbf{if } \ \langle S, s_1 \rangle \Rightarrow s'_1 \land s_1 \sim_{live_{entry}(init(S))} s_2\\
\end{cases}$$ [[TODO]]
### Corollary 1
[[TODO]]