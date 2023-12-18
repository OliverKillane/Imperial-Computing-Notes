## Definition
A variable is live at label exit if there is some path that uses its value before it is redefined.
- For each [[Program Point]] which variables need to live on
- Can be used for [[Dead Code Elimination]] and is [[Register Allocation]] (variable no longer used, can discard value and assign different variable to register)

### Kill
$$kill_{LV} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{Var}_*)$$
$$\begin{matrix*}[l c l]
kill_{LV}(&[x := a]^\ell &) = \{x\} \\
kill_{LV}(& [\mathbf{skip}]^\ell &) = \emptyset \\
kill_{LV}(& [b]^\ell &) = \emptyset \\
\end{matrix*}$$
- Kills any usages that are backpropagated to an assignment
### Generate
$$gen_{LV} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{Var}_*)$$
$$\begin{matrix*}[l c l]
gen_{LV}(&[x := a]^\ell &) = FV(a) \\
gen_{LV}(& [\mathbf{skip}]^\ell &) = \emptyset \\
gen_{LV}(& [b]^\ell &) = FV(b) \\
\end{matrix*}$$
- $gen_{LV}$ finds all usages, to be backpropagated

### Entry
$$LV_{entry} \: \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{Var}_*)$$
$$LV_{entry}(\ell) = (LV_{exit}(\ell) \setminus kill_{LV}([B]^\ell)) \cup gen_{LV}([B]^\ell) \ where \ [B]^\ell blocks(S_*)$$
### Exit
$$LV_{exit} \: \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{Var}_*)$$
$$LV_{exit}(\ell) = \begin{cases}
\emptyset & if \ \ell \in final(S_*) \\
\bigcup\{LV_{entry}(\ell') \ | \ (\ell', \ell) \in flow^R(S_*)\} & otherwise \\
\end{cases}$$
- In some other variations, all variables are considered live at termination, so the $\ell \in final(S_*)$ case would be $\mathbf{Var}_*$

## Examples
### Basic Analysis
```python
[x = 1]^1
while [y > 0]^2:
	[x = x + 1]^3
[x = 2]^4
```
$$\begin{matrix*}[l | l | l | l | l] 
\ell & gen_{LV} & kill_{LV} & LV_{entry} & LV_{exit} \\
\hline
1 & \emptyset & \{x\} & LV(1)_{exit} \setminus \{x\} & LV(2)_{entry}\\
2 & \{y\} & \emptyset & LV(2)_{exit} \cup\{y\} & LV(3)_{entry} \cup LV(4)_{entry} \\
3 & \{x\} & \{x\} & (LV(2)_{exit} \setminus \{x\}) \cup \{x\} & LV(2)_{entry} \\
4 & \emptyset & \{x\} & \emptyset & \emptyset
\end{matrix*}$$
Hence by iteration we get:
$$\begin{matrix*}[l | l | l]
\ell & LV_{entry} & LV_{exit} \\
\hline
1 & \{y\} & \{x, y\} \\
2 & \{x,y\} & \{x,y\} \\
3 & \{x,y\} & \{x,y\} \\
4 & \emptyset & \emptyset
\end{matrix*}$$
