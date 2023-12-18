## Definition
Avoiding recomputing expressions by determining the currently computed expressions at each [[Program Point]] and substituting with assignments of previous computation. Here defined on the [[While Language for Program Analysis]].
- All entries to the [[Program Point]] for a given expression must have already been computed, but not modified before the program point.
- Is a [[Forward and Backward Analysis]]
- When solving set equations, we want the largest possible sets of $AE_{entry}$ and $AE_{exit}$ that satisfy the equation for a given program so we can have the most opportunities to avoid recompilation
### Kill
$$kill_{AE} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$\begin{matrix*}[l c l]
kill_{AE}(&[x := a]^\ell &) = \{a' \in \mathbf{AExp}_* \ | \ x \in FV(a')\} \\
kill_{AE}(& [\mathbf{skip}]^\ell &) = \emptyset \\
kill_{AE}(& [b]^\ell &) = \emptyset \\
\end{matrix*}$$
Note that during assignment, we kill the currently available expressions that contain $x$.

### Generate
$$gen_{AE} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$\begin{matrix*}[l c l]
gen_{AE}(&[x := a]^\ell &) = \{a' \in \mathbf{AExp}(a)\ | \ x \not\in FV(a')\} \\
gen_{AE}(& [\mathbf{skip}]^\ell &) = \emptyset \\
gen_{AE}(& [b]^\ell &) = \mathbf{AExp}(b) \\
\end{matrix*}$$

### Entry
$$AE_{entry} \ : \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$AE_{entry}(\ell) = \begin{cases}
\emptyset & if \ \ell = init(S_*) \\
\bigcap\{AE_{exit}(\ell') \ | \ (\ell', \ell) \in flow(S_*) \} & otherwise
\end{cases}$$
Need to be conservative and take $\bigcap$ as expressions must be available from *all* input paths.
- $init$ gets the [[Extremal Labels]]
### Exit
$$AE_{exit} \ : \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{AExp}_*)$$
$$AE_{exit}(\ell) = \left( AE_{entry}(\ell) \setminus kill_{AE}\left([B]^\ell\right) \right) \cup gen_{AE}([B]^\ell) \text{ where } [B]^\ell \in blocks(S_*)$$
- exit expressions defined as $(entered - killed) + generated$ 

## Examples
### Loops

```rust
fn example(a: i32, b: i32) {
	let mut x = a + b; // P1
	let mut y = a * b;
	while y > a + b /* (a + b) is available from entries P1 and P2 */ {
		a += 1;
		x = a + b; // P2
	}
}
```

$$\begin{matrix*}[l]
[x:= a + b]^1; \\
[y := a \times b]^2; \\
\mathbf{while} \ [y > a + b]^3 \ \mathbf{do} \ ( \\
[a := a + 1]^4; \\
[x := a + b]^5; \\
); \\
\end{matrix*}$$
$$\begin{matrix*}[l | l | l ]
\ell & kill_{AE}(\ell) & gen_{AE}(\ell) \\
\hline
1 & \emptyset & \{a + b\} \\
2 & \emptyset & \{a * b\} \\
3 & \emptyset & \{a + b, y > a + b\} \\
4 & \{a+b, a*b, a+1, y> a + b\} & \emptyset \\
5 & \emptyset & \{a + b\} \\
\end{matrix*}$$
We can then create a system of equations for the $AE_{entry}$ and $AE_{exit}$ of each.

