## Definition

The assignments to variables that can reach a given point, or are available after a given point.
- A [[Forward and Backward Analysis]]
- All definitions that *could* reach the [[Program Point]]
### Kill
$$kill_{RD} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{Var}_* \times (\mathbf{Lab}_* \cup \{?\}))$$
$$\begin{matrix*}[l c l]
kill_{RD}(&[x := a]^\ell &) = \{(x, ?)\} \cup \{(x, \ell') \ | \ [B]^{\ell'} \in S_* \land B \text{ is a definition of } x \} \\
kill_{RD}(& [\mathbf{skip}]^\ell &) = \emptyset \\
kill_{RD}(& [b]^\ell &) = \emptyset \\
\end{matrix*}$$
Old definition killed on assignment.
### Generate
$$gen_{RD} \ : \ \mathbf{Block}_* \to \mathcal{P}(\mathbf{Var}_* \times (\mathbf{Lab}_* \cup \{?\}))$$
$$\begin{matrix*}[l c l]
gen_{RD}(&[x := a]^\ell &) = \{(x, \ell)\} \\
gen_{RD}(& [\mathbf{skip}]^\ell &) = \emptyset \\
gen_{RD}(& [b]^\ell &) = \emptyset \\
\end{matrix*}$$
### Entry
$$RD_{init} = \{(x, ?) \ | \ x \in FV(S_*)\} \ \text{ all variables in } S \text{ get initially defined at label }?$$
$$RD_{entry} \ : \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{Var}_* \times (\mathbf{Lab}_* \cup \{?\}))$$
$$RD_{entry}(\ell) = \begin{cases} 
RD_{init} & if \ \ell = init(S_*) \\ 
\bigcup\{RD_{exit}(\ell) \ | \ (\ell', \ell) \in flow(S_*)\} & otherwie \end{cases}$$
### Exit
$$RD_{exit} \ : \ \mathbf{Lab}_* \to \mathcal{P}(\mathbf{Var}_* \times (\mathbf{Lab}_* \cup \{?\}))$$
$$RD_{exit}(\ell) = \left( \left(RD_{entry}(\ell) \setminus kill_{RD}([B]^\ell) \right) \cup gen_{RD}([B]^\ell) \right) \ where \ [B]^\ell \in blocks(S_*)$$
We assume the program is [[While Language for Program Analysis#Label Consistency|consistent]] then this gets a single block. 

### Variations
Some assume $RD_{entry}(init(S_*)) = \emptyset$ rather than our defined $RD_{init}$ 
- This is correct only for programs that assign before first use, we consider $?$ as being defined as uninitialized.

## Equations
We can guess & iterate to get the sets of definitions for a given point
```rust
let mut m = 2; // 1
while n > 1 /* 2 */ {
	m *= n; // 3
	n -= 1; // 4;
}
// 5
```

## Examples
### Guess the Reaching Definitions
```python
# Program S
[x = 4]^1
[z = 2]^2
if [y > x]^3:
	[x = 3]^4
else:
	[x = 4]^5
[z = x]^6
```
$$\begin{matrix*}[l l | l l]
RD(1)_{entry} & = \{(x, ?), (y, ?), (z, ?)\} & RD(1)_{exit} & = \{(x, 1), (y, ?), (z, ?)\} \\
RD(2)_{entry} & = \{(x, 1), (y, ?), (z, ?)\} & RD(2)_{exit} & = \{(x, 1), (y, ?), (z, 2)\} \\
RD(3)_{entry} & = \{(x, 1), (y, ?), (z, 2)\} & RD(3)_{exit} & = \{(x, 1), (y, ?), (z, 2)\} \\
RD(4)_{entry} & = \{(x, 1), (y, ?), (z, 2)\}  & RD(4)_{exit} & = \{(x, 4), (y, ?), (z, 2)\} \\
RD(5)_{entry} & = \{(x, 1), (y, ?), (z, 2)\} & RD(5)_{exit} & = \{(x, 5), (y, ?), (z, 2)\}\\
RD(6)_{entry} & = \{(x, 4),(x, 5), (y, ?), (z, 2)\}  & RD(6)_{exit} & = \{(x, 4),(x, 5), (y, ?), (z, 6)\} \\
\end{matrix*}$$
- Constant propagation of $x:= 4$ to $y > x$
- Very busy expression analysis

```python
x = 4
z = 2
if y > x:
	x = 3
else:
	x = 3
z = x
```
Same as previous question.

### Construct RD Equations
```python
[x = 4]^1
[z = 2]^2
if [y > x]^3:
	[x = 3]^4
else:
	[x = 4]^5
[z = x]^6
```
Hence we get the flow:
$$flow(S) = \{ (1,2), (2,3), (3,4), (3,5), (4,6), (5,6) \}$$
Can then get for each:
$$\begin{matrix*}[l |l | l | l | l]
\ell & gen_{RD} & kill_{RD} & RD{entry} & RD_{exit} \\
\hline
1 & \{(x,1)\} & \{(x,?),(x,2),(x,3),(x,1)\}
\end{matrix*}$$
$$\begin{matrix*}[l l | l l]
RD(1)_{entry} & = RD_{init} & RD(1)_{exit} & =  \\
\end{matrix*}$$
[[TODO]]
### Create a program wit reaching definitions
$$\{(x,1),(x,4),(x,8)\} \subseteq RD_{entry}(9)$$
```python
if ...:
	[x = ...]^1
else:
	if ...:
		[x = ...]^4
	else:
		[x = ...]^8
[...]^9
```
For the following, there is no while program
$$\{(x,3),(y,3)\} \subseteq RD_{entry}(...)$$
As we cannot define multiple variables in one block, we cannot construct this.