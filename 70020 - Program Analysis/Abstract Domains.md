## Definition
- Can be compared with the [[Fun Language for Program Analysis#Concrete Domain]].
### Abstract Environment
$$\widehat{\rho} \in \widehat{\mathbf{Env}} = \mathbf{Var} \to \widehat{\mathbf{Val}}$$
- Maps variables to an abstract value
### Abstract Cache
$$\widehat{C} \in \widehat{\mathbf{Cache}} = \mathbf{Lab} \to \widehat{\mathbf{Val}}$$
### Abstract Value
$$\widehat{v} \in \widehat{\mathbf{Val}} = \mathcal{P}(\mathbf{Term})$$
- A set of terms of the form $\mathbf{fn} \ x \Rightarrow e_0$
