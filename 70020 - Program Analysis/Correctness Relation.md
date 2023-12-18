## Definition
We can directly relate properties to values with a [[Correctness Relation]]
$$\textcolor{red}{\triangleright} : \mathcal{V} \times \mathcal{L} \to \{\mathbf{tt}, \mathbf{ff}\} \text{ or as a set } \textcolor{red}{\triangleright} \subseteq \mathcal{V} \times \mathcal{L}$$
- $v \textcolor{red}{\triangleright} l$ means $v$ is described by property $l$
## Preservation under Computation
$$\left( v_1 \textcolor{red}{\triangleright} l_1 \land S \left(\vdash v_1 \to v_2 \right) \land \left(S \vdash l_1 \rightsquigarrow l_2 \right)\right) \Rightarrow v_2 \textcolor{red}{\triangleright} l_2  $$
## [[Complete Lattice]] on $\mathcal{L}$
When the set of properties $\mathcal{L} = (\mathcal{L}, \sqsubseteq, \sqcup, \sqcap, \bot, \top)$
$$v \textcolor{red}{\triangleright} l_1 \land l_1 \sqsubseteq l_2  \Rightarrow v \textcolor{red}{\triangleright} l_2 $$
- Here *smaller* properties are considered more precise, hence we can cut down to this more precise property.
- The decision to have *more precise $=$ smaller* is arbitrary
$$\forall l \in \mathcal{L'} \subseteq \mathcal{L} : v \textcolor{red}{\triangleright} l \Rightarrow  v \textcolor{red}{\triangleright} \sqcap \mathcal{L}'$$
- There is always a *smallest*/most precise property, of the set of properties applicable.
- As a result of this: $$v \textcolor{red}{\triangleright} \top \quad \text{ and } \quad \left( v \textcolor{red}{\triangleright} l_2 \land v \textcolor{red}{\triangleright} l_2 \right) \Rightarrow \left( v \textcolor{red}{\triangleright} \left(l_1 \sqcap l_2\right) \right)$$
## Transformation from $\mathcal{V}$
- We can use a [[Representation Function]] $\beta$ to induce a [[Galois Connection]] $(\mathcal{P}(\mathcal{V}), \alpha, \gamma, \mathcal{L})$ $$\beta : \mathcal{V} \to \mathcal{L} \quad \text{ where } \quad \begin{split} \alpha(V) & = \bigsqcup\{\beta(v) \ | \ v \in V\} \\ \gamma(l) & = \{v \in V \ | \ \beta(v) \sqsubseteq l\}\\ \end{split}$$
- We can use an [[Extraction Function]] $\eta$ $$\eta : \mathcal{V} \to \mathcal{D} \quad \text{ where } \quad \begin{split}\alpha(V) &= \{\eta(v) \ | \ v \in V\} \\ \gamma(D) & = \{v \ | \ \eta(v) \in D\} \end{split}$$
