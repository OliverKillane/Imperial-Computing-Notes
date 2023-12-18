## Definition
Requires [[Abstract Domains]] and a specification of the analysis to produce $(\widehat{C}, \widehat{\rho})$
- $\widehat{C}$ is an [[Abstract Domains#Abstract Cache]] (*shape* of the label)
- $\widehat{\rho}$ is the [[Abstract Domains#Abstract Environment]] that associates values with each variable (*shape* of the variables)
We have the entails relation:
$$\vDash \ : (\widehat{\mathbf{Cache}} \times \widehat{\mathbf{Env}} \times \mathbf{Exp}) \to \{true, false\}
 \qquad \qquad (\widehat{C}, \widehat{\rho}) \vDash e$$ Which means we have an acceptable [[Control Flow Analysis]]for expression $e$.
- If a subexpression $t^\ell$ evaluates to a closure, then the closure must be predicted by $\widehat{C}(\ell)$

This analysis is not [[Context Sensitive]] and in [[Control Flow Analysis]] terminology is [[Monovariant]].
## Rules
### Constants
$$(\widehat{C}, \widehat{\rho}) \vDash_s c^\ell \quad \text{always}$$
Since we care about closures only, constants are irrelevant.
### Terms
$$(\widehat{C}, \widehat{\rho}) \vDash_s x^\ell \Longleftrightarrow \widehat{\rho}(x) \subseteq \widehat{C}(\ell)$$
The variable contains the same value as is predicted by the [[Abstract Domains#Abstract Cache|cache]].
### if-else
$$(\widehat{C}, \widehat{\rho}) \vDash_s \left[\mathbf{if} \ t_0^{\ell_0} \ \mathbf{then} \ t_1^{\ell_1} \ \mathbf{else} \ t_2^{\ell_2}\right]^\ell \ \Longleftrightarrow \begin{split} 
& (\widehat{C}, \widehat{\rho}) \vDash_s t_0^{\ell_0} \land (\widehat{C}, \widehat{\rho}) \vDash_s t_1^{\ell_1} \land (\widehat{C}, \widehat{\rho}) \vDash_s t_2^{\ell_2} \\
\land & \ \widehat{C}(\ell_1) \subseteq \widehat{C}(\ell) \\
\land & \ \widehat{C}(\ell_2) \subseteq \widehat{C}(\ell)
\end{split}$$
The [[Abstract Domains#Abstract Cache|cache]] must contain the terms for both branches (& whence what this label could be).
### Let
$$(\widehat{C}, \widehat{\rho}) \vDash_s \left[ \mathbf{let} \ x = t_1^{\ell_1} \ \mathbf{in} \ t_2^{\ell_2} \right]^\ell \Longleftrightarrow \begin{split} 
& (\widehat{C}, \widehat{\rho}) \vDash_s t_1^{\ell_1} \land (\widehat{C}, \widehat{\rho}) \vDash_s t_2^{\ell_2}\\
\land & \ \widehat{C}(\ell_1) \subseteq \widehat{\rho}(x) \\
\land & \ \widehat{C}(\ell_2) \subseteq \widehat{C}(\ell) \\
\end{split}$$
Like with [[0-CFA Analysis#if-else|if-else]] we need the [[Abstract Domains#Abstract Cache|cache]] to have the *shape* of $\ell$, but now we need to ensure that $\widehat{\rho}$ also has the shape of $x$.
### Operator
$$(\widehat{C}, \widehat{\rho}) \vDash_x \left[ t_1^{\ell_1} \ op \ t_2^{\ell_2} \right]^\ell \Longleftrightarrow (\widehat{C}, \widehat{\rho}) \vDash_s t_1^{\ell_1} \land (\widehat{C}, \widehat{\rho}) \vDash_s t_2^{\ell_2}$$
$\widehat{C}$ must have the shape of both sides, as $op$ is assumed to be $+,-,\times, \div$ we assume its shape is not a closure.
### Closure
$$(\widehat{C}, \widehat{\rho}) \vDash_x \left[\mathbf{fn} \ x \Rightarrow e_0 \right]^\ell \Longleftrightarrow \{\mathbf{fn} \ x \Rightarrow e_0\} \subseteq \widehat{C}(\ell) \land (\widehat{C}, \widehat{\rho}) \vDash_s e_0$$
We can include $\ell$ in $\widehat{C}$ because we assume [[Label Consistency]].
### Application
$$(\widehat{C}, \widehat{\rho}) \vDash_x \left[ t_1^{\ell_1} \ t_2^{\ell_2}\right]^\ell \Longleftrightarrow \begin{split} 
& (\widehat{C}, \widehat{\rho}) \vDash_s t_1^{\ell_1} \land (\widehat{C}, \widehat{\rho}) \vDash_s t_2^{\ell_2} \\
\land & \left( \forall (\mathbf{fn} \ x \Rightarrow t_0^{\ell_0}) \in \widehat{C}(\ell_1) : \widehat{C}(\ell_2) \subseteq \widehat{\rho}(x) \land \widehat{C}(\ell_0) \subseteq \widehat{C}(\ell) \right) \\
\end{split}$$

