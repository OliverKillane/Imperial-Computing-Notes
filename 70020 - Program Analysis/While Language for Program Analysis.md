We can define a basic while language as the following:
$$\begin{split} 
a & \in \mathbf{AExp} \ & \text{(Arithmetic Expressions)}\\ 
b & \in \mathbf{BExp} & \text{(Boolean Expressions)} \\ 
S & \in \mathbf{Stmt} & \text{(Statements)}\end{split}$$
Defined as:
$$\begin{split}
a & ::= x \ | \ n \ | \ a_1 \ op_a \ a_2  \\ 
b & := true \ | \ false \ | \ not \ b \ | \ b_1 \ op_b \ b_2 \ | \ a_1 \ op_r \ a_2 \\
S & ::=  x := a \ | \ \mathbf{skip} \ | \ S_1;S_2 \ | \ \mathbf{if} \ b \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 \ | \ \mathbf{while} \ b \ \mathbf{do} \ S 
\end{split}$$
If we need to label statements, we can express this as:
$$S ::= [x := a]^\ell \ | \ S_1;S_2 \ | \ \mathbf{if} \ [b]^\ell \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 \ | \ \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S$$
We can also avoid using [[meta symbols]] with a concrete syntax as $$\dots \ | \ \mathbf{if} \ b \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 \ \mathbf{fi} \ | \ \mathbf{while} \ b \ \mathbf{do} \ S \ \mathbf{od}$$ 

The symbol $op$ is defined as:
$$\begin{split} 
op_a & \in \mathbf{Op}_a \ & \text{(Arithmetic operators such as }  +, \times, -\text{)} \\
op_b & \in \mathbf{Op}_b \ & \text{(Boolean operators such as } \land, \lor, \Rightarrow, \dots \text{)} \\
op_r & \in \mathbf{Op}_r \ & \text{(Relational operators such as } >, <, \leq, =, \dots \text{)} \\
\end{split}$$
A finite number of symbols is given as:
$$\begin{split} 
x, y, z, \dots & \in \mathbf{Var} \ & \text{(Variables)} \\
n, m, \dots, & \in \mathbf{Num} \ & \text{(Numerals)} \\
\ell, \dots & \in \mathbf{Lab} \ & \text{(Labels)} \\
\end{split}$$

When dealing with an entire program, we use $S_*$ to represent the *top-level statement*/whole program. Given program $S_*$ we use the notation:
$$\begin{split}
\mathbf{Lab}_* & = labels(S_*) \\
\mathbf{Var}_* & = FV(S_*) \\
\mathbf{Block}_* & = blocks(S_*) \\
\mathbf{AExp}_* & = \text{ Non-Trivial arithmetic expressions} \\
\end{split}$$
> [!NOTE]  
> $AExp$ gives the set of non-trivial arithmetic expressions for a given arithmetic. For example $AExp(a)$ for some $x := a$, or $AExpr(b)$ for boolean arithmetic $\mathbf{if} \ b \dots$

## Interacting with While
### Initial Label
$$init \ : \ \mathbf{Stmt} \to \mathbf{Lab}$$
$$\begin{matrix*}[l c r l]
init(& [x:=a]^\ell& ) & = \ell \\
init(& [\mathbf{skip}]^\ell & ) & = \ell \\
init(& S_1;S_2 & ) & = init(S_1) \\
init(& \mathbf{if} \ [b]^\ell \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 &) & = \ell \\
init(& \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S &) & = \ell \\
\end{matrix*}$$
### Final Label
$$final \ : \ \mathbf{Stmt} \to \mathcal{P}(\mathbf{Lab})$$
$$\begin{matrix*}[l c l l]
final( & [x := a]^\ell & ) & = \{\ell\} \\
final( & [\mathbf{skip}]^\ell  & ) & = \{\ell\} \\
final( & S_1;S_2 & ) & = final(S_2) \\
final( & \mathbf{if} \ [b]^\ell \ \mathbf{then} S_1 \ \mathbf{else} \ S_2 & ) & = final(S_1) \cup final(S_2) \\
final( & \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S & ) & = \{\ell\} \\
\end{matrix*}$$
### Blocks
A $\mathbf{Block}$ is a set of statements of the form $[x := a]^\ell \ | \ [\mathbf{skip}]^\ell \ | \ [b]^\ell$.
$$blocks \ : \ \mathbf{Stmt} \to \mathcal{P} (\mathbf{Block})$$
$$\begin{matrix*}[l c l l]
blocks( & [x := a]^\ell & ) & = \{ [x := a]^\ell \} \\
blocks( & [\mathbf{skip}]^\ell & ) & = \{ [\mathbf{skip}]^\ell \} \\
blocks( & S_1;S_2 & ) & = blocks(S_1) \cup blocks(S_2) \\
blocks( & \mathbf{if} \ [b]^\ell \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 & ) & = \{ [b]^\ell \} \cup blocks(S_1) \cup blocks(S_2) \\
blocks( & \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S & ) & = \{ [b]^\ell \} \cup blocks(S) \\
\end{matrix*}$$
### Labels
$$labels \ : \ \mathbf{Stmt} \to \mathcal{P}(\mathbf{Lab})$$
$$labels (S) = \{\ \ell \ | \ [B]^\ell \in blocks(S)\}$$
Hence $\forall S. \ init(S) \in labels(S) \land final(S) \subseteq labels(S)$.

- We can also define labels as: $$labels(S) = \{init(S)\} \cup \{\alpha \ | \ (\alpha, \beta) \in flow(S)\} \cup \{ \beta \ | \ (\alpha, \beta) \in flow(S)\}$$
- We can also remove the $\{init(S)\}$ for composite statements (e.g. $S = S_1;S_2$)
- $flow$ is used for [[Forward and Backward Analysis]], and $flow^R$ for backward analysis
### Flow
The set of arcs between nodes in the control flow graph as $(\ell_1,  \ell_2)$ pairs.
$$flow \ : \ \mathbf{Stmt} \to \mathcal{P}(\mathbf{Lab} \times \mathbf{Lab})$$
$$\begin{matrix*}[l c l l]
flow(& [x := a]^\ell &) & = \emptyset \\
flow(& [\mathbf{skip}]^\ell &) & = \emptyset \\
flow(& S_1;S_2 &) & = flow(S_1) \cup flow(S_2) \cup \{(\ell, init(S_2)) \ | \ l \in final(S_1) \}\\
flow(& \mathbf{if} \ [b]^\ell \ \mathbf{then} \ S_1 \ \mathbf{else} \ S_2 &) & = flow(S_1) \cup flow(S_2) \cup \{(\ell, init(S_1)), (\ell, init(S_2))\}\\
flow(& \mathbf{while} \ [b]^\ell \ \mathbf{do} \ S &) & = flow(S) \cup \{(\ell, init(S))\} \cup \{(\ell', \ell) \ | \ \ell' \in final(S)\} \\
\end{matrix*}$$
we can also derive a reverse flow as: $$ flow^R(S) \ = \{(\alpha, \beta) \ | \ (\beta, \alpha) \in flow(S)\}$$
## Properties
[[Isolated Entries & Exits]] and [[Label Consistency]]

## Examples
### Labelling flow for a program
```python
# Program S
[x = 1]^1
while [y > 0]^2:
	if [y <= 0]^3:
		[x := x + 3]^4
	else: 
		[pass]^5
	[x = x - 1]^6
	[z = z + x]^7
[x = 2]^8
```
$$
\begin{split}
flow(S) & = \{(1,2), (2,3), (3,4), (3,5), (4,6), (5,6), (6,7), (7,8), (7,2)\} \\
flow(S) & = \{(2,1), (3,2), (4,3), (5,3), (6,4), (6,5), (7,6), (8,7), (2,7)\} \\
\end{split}$$
We can simplify this with regards to $y > 0$ as:
- If inside the loop, we know that $\ell^3$ is false, and thus we always evaluate the `else` branch.
- The `else` branch is empty, so we can reduce to $(2,6) \in flow(S)$
As $y$ is not assigned to in the loop, we could simplify this to:
```python
x = 1
if y > 0:
	while True:
		x = x - 1
		z = z + x
x = 2
``` 
We could then reduce this further, as $z$ is decremented infinitely, and $x = 2$ dominates the output of the program, we could get:
```python
if y > 0:
	z = -infinity
x = 2
```

> [!NOTE]  
> I'm not sure if this is the answer wanted, I skirted analysing predicates generally.
### Formally Construct Flow
```python
[x = 1]^1
if [x > 0]^2:
	[x = x - 1]^3
else:
	[y = y - 1]^4
```
$$\begin{split} 
flow(S) & = flow([x:= 1]) \cup flow(if \ x > 0 \ then \ x = x - 1 \ else \ y = y - 1) \cup \{(1, 2)\} \\
& = \emptyset \cup flow(if \ x > 0 \ then \ x = x - 1 \ else \ y = y - 1) \cup \{(1, 2)\} \\
& = \{1,2\} \cup \{(2,3),(2,4)\} \\
& = \{(1,2),(2,3),(2,4)\} \\
\end{split}$$
### Guess the reaching def
[[TODO]]
