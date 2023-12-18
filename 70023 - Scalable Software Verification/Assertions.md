## Definition
$$\begin{split}
(\forall e,s,h. \ e,s,h \vDash P) & \Longleftrightarrow \ \vdash  P \\
(\forall e,s,h. \ e,s,h \vDash P \Longrightarrow e,s,h \vDash Q) & \Longleftrightarrow P \vdash Q \\
\end{split}$$
- $\vdash$ declares an assertions entails another.
- If anything entails an assertion, the assertion is valid (e.g $\vdash True$).
- $\vDash$ declares the assertions are valid given a [[Logical Environment]], [[Variable Store]] and [[Heap]]
## Logical Values & Expressions
$$LVal \text{ ranged over by } a_1, a_2, a_3, \dots \text{ which are elements of } Val$$
$$LExp ::= a \ | \ x \ | \ \mathbf{x} \ | \ E + E \ | \ E - E \ | \ E : E \ | \ E  \ \bullet \ E \ | \ E = E \ | \ E > E \ | \ E \in X \ | \ E \land E \ | \ \dots $$
Similar to [[While Language for Separation Logic#Expressions]], but with $LVar$ logical variables in addition to regular variables, lists and $\bullet$ 
## Syntax
Logical expressions have a similar  syntax, assertions include the following:
$$\begin{matrix*}[r r r l l] 
P \in Assert & ::= && P \land P \ | \ P \Rightarrow P \ | \ True \ | \ False \\
&& | & E=E \ | \ E > E \ | \ E \in X \ | \ \dots \\
&& | & \exists x . P \\
&& | & P \star P \ | \ P \mathrlap{\rightarrow} \ \star P \ | \ emp \ | \ \mathrlap{\bigcirc} * \ _{E_1 \leq x < E_2} P \\
&& | & E \mapsto E \\ 
\end{matrix*}$$
A $LEnv \triangleq LVar \rightharpoonup_{fin} LVal$ logical environment maps logical variables just like regular variables from the [[Variable Store]].
- Includes the [[Heap#Cell Assertion|cell assertion]]