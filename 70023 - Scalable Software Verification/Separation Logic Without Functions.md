## Rules
> [!NOTE]  
> We use $x$ for the [[Logical Variable]]s and $\underline{x}$ for the program variables from the [[Variable Store]]
### Assign
$$\cfrac{\underline{x} \not\in pv(E_{old})}{\vdash\{ \underline{x} \overset{.}{=} E_{old} \star E_{new} \overset{.}{\in} Val\} \ \underline{x} := E_{new} \ \{\underline{x} \overset{.}{=} E_{new}[E_{old} / \underline{x}]\} }$$
Given some $x$ which is $E_{old}$ we can assign $E_{new}$ to $x$ if:
- $E_{new}$ is an expression that can be evaluated (see the [[Satisfiability Relation]])
- We replace $\underline{x}$ in $E_{old}$ for the new $\underline{x}$ (avoid recursive expression)
### Lookup
$$\cfrac{\underline{x} \not\in pv(E')}{\vdash \{\underline{x} \overset{.}{=} E' \star E \mapsto E_1 \} \ \underline{x} := [E_{new}] \ \{ \underline{x} \overset{.}{=} E_1[E'/\underline{x}] \star E[E'/\underline{x}] \mapsto E_1[E'/\underline{x}] \}}$$
- We replace where the old value of $x$ may have been used.
- Dereference $E$ to get the value, assign to $\underline{x}$
- We keep the postcondition that the original $E$ (using old $x$) $\mapsto E_1$ (again replacing $x$ as we are updating it)
### Mutate
$$\cfrac{}{
\vdash \{E_1 \mapsto E \star E_2 \overset{.}{\in} Val\} \ [E_1] := E_2 \ \{E_1 \mapsto E_2\}  
}$$
- Create new mapping, $E_2$ must be expression that can be evaluated.
### New
$$\cfrac{\underline{x} \not\in pv(E')}{\vdash \{\underline{x} \overset{.}{=} E' \star E \overset{.}{\in} \mathbb{N}\} \ \underline{x} := new (E) \ \{\exists x . \ \underline{x} \overset{.}{=} x \star \mathrlap{\bigcirc} * \ _{0 \leq i < E[E'/\underline{x}]}\ ((x+i) \mapsto null) \}}$$
- Set the physical variable $\underline{x}$ to the pointer to the start of the allocation, and ensure that each cell afterwards (of size of the allocation) contains null and is present.
```C
x = calloc(E);
```
### Dispose
$$\cfrac{}{\{E \mapsto E_1 \} \ dispose(E) \ \{emp\}}$$
- Only disposes of a single cell, for multi-cell allocations ($new(E)$ where $E > 1$) we need a loop.
$$\underline{e} := E; \underline{x} := new(e); \underline{i} := 0; while \ (\underline{i} < \underline{e}) \ do \ ( dispose(\underline{x} + \underline{i}); \underline{i} := \underline{i} + 1 ) $$
### Control Flow
$$\cfrac{\vdash \{P \land E\} \ C_1 \ \{Q_1\} \qquad \vdash \{P \land \neg E\} \ C_2 \ \{Q_2\}}{\vdash \{P \star E \overset{.}{\in} Bool\} \ if \ (E) \ C_1 \ else \ C_2 \ \{Q_1 \lor Q_2\}}\qquad (If)$$
$$\cfrac{\vdash \{P \land E\} \ C \ \{P \star E \overset{.}{\in} Bool\}}{
\vdash \{P \star E \overset{.}{\in} Bool\} \ while \ (E) \ C \ \{P \land \neg E\}
} \qquad (While)$$
$$\cfrac{}{\vdash \{emp\} \ skip \ \{emp\}} \qquad (Skip)$$
$$\cfrac{\vdash \{P\} \ C_1 \ \{Q\} \qquad \{Q\} \ C_2 \ \{R\}}{
\vdash \{P\} \ C_1;C_2 \ \{R\}
} \qquad (Seq)$$
### Frame
$$\cfrac{\vdash \{P\} \ C \ \{Q\} \qquad mod(C) \cap pv(R) = \emptyset}{
\vdash \{P \star R\} \ C \ \{Q \star R\}
}$$
- We can separate one side of the $P \star R$ provided the computation $C$ does not affect any [[Variable Store|variables]]  in $R$
### Cons
$$\cfrac{
\vdash P \Rightarrow P' \quad \vdash \{P'\} \ C \ \{Q'\} \quad Q' \Rightarrow Q
}{
\vdash \{P\} \ C \ \{Q\}
}$$
We can weaken by implication.
### Exists
$$\cfrac{\vdash \{P\} \ C \ \{Q\}}{
\vdash \{\exists x. \ P\} \ C \ \{\exists x . \ Q\}
}$$
We can weaken an assertion with a [[Logical Variable]] introduced 
### Disj
$$\cfrac{\vdash \{P_1\} \ C \ \{Q\} \qquad \vdash \{P_2\} \ C \ \{Q\}}{
\vdash \{P_1 \lor P_2\} \ C \ \{Q\}
}$$
We can also add in derived rules for $\lor$ and $\land$
$$\cfrac{\vdash \{P_1\} \ C \ \{Q_1\} \qquad \vdash \{P_2\} \ C \ \{Q_2\}}{\vdash \{P_1 \lor P_2\} \ C \ \{Q_1 \lor Q_2\}} \qquad (Disj')$$
Attainable by using for both cases from $Disj$ ($\{P_1\} \ C \ \{Q_1 \lor Q_2\}$) with $Cons$ and $Q_1 \Rightarrow Q_1 \lor Q_2$ to weaken. 
$$\cfrac{\vdash \{P_1\} \ C \ \{Q\} \qquad \vdash \{P_2\} \ C \ \{Q\}}{\vdash \{P_1 \land P_2\} \ C \ \{Q\}} \qquad (Conj)$$
### Global Assign
A derived assignment + assertion:
$$\cfrac{x \not\in flv(P)}{
\vdash \{\underline{x} \overset{.}{\in} Val \star E \overset{.}{\in} Val \star P\} \ \underline{x} := E \ \{\forall x. \underline{x} \overset{.}{=} E[x/\underline{x}] \star P[x/\underline{x}]\}
}$$
- where $flv$ gets free logical variables.
- Allows an assertion to be included that contains $\underline{x}$
- Derived as using $cons \to exists \to frame \to assign$