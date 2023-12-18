## Forward Analysis
We can express forward and [[Data Flow Analysis]] 

| | Forward | Backward |
|-|-|-|
|Flow| $F = flow(S_*)$ | $F = flow^R(S_*)$ |
| [[Isolated Entries & Exits]]| Entries | Exists |
|Exit Conditions| $Analysis_\bullet(\ell)$|$Analysis_\circ(\ell)$|
|Entry Conditions| $Analysis_\circ(\ell)$|$Analysis_\bullet(\ell)$|

For all we have:
- $E$ is the [[Extremal Labels]]
- $\iota$ is the [[Extremal Value]]
- $f_\ell$ is the [[Transfer Function]]
- $\bigsqcup$ is either $\cap$ ([[Must Analysis]]) or $\cup$ ([[May Analysis]]) 
## Classical Formulation
We can describe some of the [[Data Flow Analysis]] in terms of forward/backward analysis.
- Assuming [[Isolated Entries & Exits|isolated entries]] for forward and [[Isolated Entries & Exits|isolated exists]] for backwards.
$$\begin{split} 
Analysis_\circ(\ell) & = \begin{cases}
\iota & if \ \ell \in E \\ 
\sqcup\{Analysis_\bullet(\ell') \ | \ (\ell', \ell) \in F\} & if \ \ell \not\in E \\
\end{cases} \\
Analysis_\bullet(\ell) & = f_\ell(Analysis_\circ(\ell)) \\
\end{split}$$
## Alternative Definition
We can weaken to remove the requirement for [[Isolated Entries & Exits]] be reformulating as, given $\bot \text{ satisifes } I \sqcup \bot = I$:
$$\begin{split} 
Analysis_\circ(\ell) & = \sqcup \{Analysis_\bullet(\ell') \ | \ (\ell', \ell) \in F\} \sqcup \iota^\ell_E  \\
Analysis_\bullet(\ell) & = f_\ell(Analysis_\circ(\ell)) \\
\end{split} \ \text{ where } \ \iota^\ell_E = \begin{cases} 
\iota & if \ \ell \in E \\
\bot & if \ \ell \not\in E \\ 
\end{cases}$$
