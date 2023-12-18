## Definition
An expression is very busy if at the exit from a label, all paths must always use the value, before any of the variables used in the expression are redefined/reassigned.
```rust
// could hoist a + b * 3 up to here.
if foo {
	// no assignment to a or b
	let mut y = a + b * 3;
	// ...
} else {
	// no assignment to a or b
	let mut z = a + b * 3;
	// ...
}
```
- For each [[Program Point]] which expressions must be busy at exit.
- A [[Backward Analysis]]
### Kill
$$kill_{VB} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$\begin{matrix*}[l c l]
kill_{VB}(&[x := a]^\ell &) = \{a' \in \mathbf{AExp}_* \ | \ x \in FV(a')\} \\
kill_{VB}(& [\mathbf{skip}]^\ell &) = \emptyset \\
kill_{VB}(& [b]^\ell &) = \emptyset \\
\end{matrix*}$$
This is identical to [[Available Expressions]]
### Gen
$$gen_{VB} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$\begin{matrix*}[l c l]
gen_{VB}(&[x := a]^\ell &) = \mathbf{AExp}(a) \\
gen_{VB}(& [\mathbf{skip}]^\ell &) = \emptyset \\
gen_{VB}(& [b]^\ell &) = \mathbf{AExp}(b) \\
\end{matrix*}$$
### Entry
$$AE_{entry} \ : \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$VB_{entry}(\ell) = (VB_{exit}(\ell) \setminus kill_{VB}([B]^\ell)) \cup gen_{VB}([B]^\ell) \ where \ [B]^\ell \in blocks(S_*)$$
### Exit
$$AE_{exit} \ : \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$BV_{exit}(\ell) = \begin{cases} 
\emptyset & if \ \ell \in final(S_*) \\ 
\bigcap\{VB_{entry}(\ell') \ | \ (\ell', \ell) \in flow^R(S_*)\} & otherwise \\
\end{cases}$$
Backpropagate busy definitions from the entry of the next blocks.