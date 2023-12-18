## Definition
$$\text{Let } \mathcal{C} = (\mathcal{C}, \leq_{\mathcal{C}}) \text{ and } \mathcal{D} = (\mathcal{D}, \leq_{\mathcal{D}}) \text{ with } \alpha : \mathcal{C} \to \mathcal{D} \text{ and } \gamma : \mathcal{D} \to \mathcal{C} $$
where both are [[Partial Order|partially ordered sets]] with order-preserving conversion function s $\alpha: \mathcal{C} \to \mathcal{D}$ and $\gamma : \mathcal{D} \to \mathcal{C}$.
$$\forall c \in \mathcal{C}, d \in \mathcal{D} : c \leq_{\mathcal{C}} \gamma(d) \Leftrightarrow \alpha(c) \leq_{\mathcal{D}} d $$
- $\alpha$ is the abstraction and $\gamma$ is the concretisation
- $\alpha \circ \gamma$ is a [[Reductive Function]] ($\forall d: (\alpha \circ \gamma)(d) \leq_{\mathcal{D}} d$)
- $\gamma \circ \alpha$ is an [[Extensive Function]] ($\forall c: c \leq_{\mathcal{C}}(\gamma \circ \alpha)(c)$)

Then we have [[Galois Connection]] $(\mathcal{C}, \alpha, \gamma, \mathcal{D})$
- $\alpha$ and $\gamma$ are [[Quasi-Inverse]] $\alpha \circ \gamma \circ \alpha = \alpha \land \gamma \circ \alpha \circ \gamma = \gamma$

## Examples
### Sign
[[TODO]]