## Definition
Each [[Hoare-Triple]] comes with a [[Function Specification Context]] $\Gamma$ .
- Included in the program definition $(\gamma, C)$
## Validity
$$\Gamma \vdash \{P\} \ C \ \{Q\}$$

Command specification $\{P\} \ C \ \{Q\}$ is valid in [[Function Specification Context]] $\Gamma$
$$(\gamma, \Gamma) \vdash \{P\} \ f( \ \overrightarrow{x} \ ) \ \{Q\}$$
The [[Function Specification]] is valid in the [[Function Specification Environment]] $(\gamma, \Gamma)$
$$\vdash (\gamma, \Gamma)$$
The [[Function Specification Environment]] is valid.
$$\Gamma \vdash \{P\} \ \{\gamma, \Gamma\} \ \{Q\}$$
The program specification is valid given the [[Function Specification Context]] $\Gamma$
## Rules
In addition to the rules from [[Separation Logic Without Functions]] (with the $\Gamma$ added before $\vdash$ for these rules).
### Function Call
$$\cfrac{
\{P\} \ f ( \ \overrightarrow{x} \ ) \ \{Q\} \in \Gamma
}{
\Gamma \vdash \left\{ \overrightarrow{E} \overset{.}{\in} Val \star P\left[ \ \overrightarrow{E} \ / \ \overrightarrow{x} \ \right] \right\} \ y := f(\overrightarrow{E}) \ \{Q[y/ret]\}
} \qquad (fcall)$$
The [[Function Specification Context]] needs to have the correct pre & post conditions for the function.
### Verifying a Function Definition
$$\cfrac{
f(\overrightarrow{x}) \{C; \ return \ E\} \in \gamma \qquad \{P\} \ f(\overrightarrow{x}) \{Q\} \in \Gamma \qquad \{\overrightarrow{z}\} = pv(C)/\{\overrightarrow{x}\} \qquad \Gamma \vdash \{P \star \overrightarrow{z} \overset{.}{=} null\} \ C \ \{Q[E/ret]\}
}{
(\gamma, \Gamma) \vdash \{P\} \ f(\overrightarrow{x}) \ \{Q\}
} \qquad (func)$$
- The function must have a definition (in $\gamma$) that returns some expression $E$.
- It must also have a context in $\Gamma$
- We can then check the function definition $C$ with all non-parameter variables set to $null$, and ensuring it returns $E$
### [[Function Specification Environment]]
$$\cfrac{
\{P\} \ f(\overrightarrow{x}) \ \{Q\} \in \Gamma \Longrightarrow (\gamma, \Gamma) \vdash \{P\} \ f(\overrightarrow{x}) \ \{Q\} 
}{
\vdash (\gamma, \Gamma)
} \qquad (Env) $$
- Given some pre & post conditions in  $\Gamma$, we can use it with the $\gamma$
### Programs
$$\cfrac{
\vdash (\gamma, \Gamma) \qquad \Gamma \vdash \{P\} \ C \ \{Q\}
}{
\Gamma \vdash \{P\} \ (\gamma, C) \ \{Q\}
}$$
- Given some valid [[Function Specification Environment]] and some program $(\gamma, C)$ we can apply separation logic to get $Q$ from $P$.