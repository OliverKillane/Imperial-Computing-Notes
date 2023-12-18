### Definition
If the reaching definition of a variable is constant and equal for all $RD_{entry}$ .
- Uses [[Reaching Definitions]]
$$RD \vdash [x := a]^\ell \ \triangleright \ [x := a[y \mapsto n]]^\ell \ if \ \begin{cases} y \in FV(a) & \text{y is used in a} \\ \land \ (y, ?) \not\in RD_{entry}(\ell) & \text{y not from input} \\ \land \ \forall(y', \ell') \in RD_{entry}(\ell) . y' = y \Rightarrow [\dots]^{\ell'} = [y := n]^{\ell'} & \text{Assigned same constant} \end{cases} $$
$$RD \vdash [x := a]^\ell \triangleright [x := n]^\ell \ if \begin{cases} FV(a) = \emptyset & \text{ no inputs used} \\ \land \ \ a \text{ not a constant} & \\ \land \ \ eval(a) = n & \text{ constant evaluation} \end{cases}$$
$$\cfrac{RD \vdash S_1 \ \triangleright \ S'_1}{RD \vdash S_1;S_2 \ \triangleright S'_1;S_2}$$
$$\cfrac{RD \vdash S_2 \ \triangleright \ S'_2}{RD \vdash S_1;S_2 \ \triangleright S_1;S'_2}$$
$$\cfrac{RD \vdash S_1 \ \triangleright \ S'_1}{RD \vdash if \ [b]^\ell \ then \ S_1 \ else \ S_2 \ \triangleright \ if \ [b]^\ell \ then \ S'_1 \ else \ S_2}$$
$$\cfrac{RD \vdash S_2 \ \triangleright \ S'_2}{RD \vdash if \ [b]^\ell \ then \ S_1 \ else \ S_2 \ \triangleright \ if \ [b]^\ell \ then \ S_1 \ else \ S'_2}$$
$$\cfrac{RD \vdash S \triangleright S'}{RD \vdash while \ [b]^\ell \ do \ S \ \triangleright \ while \ [b]^\ell \ do \ S'}$$
We need to be careful about recalculating reaching definitions after rewriting
- Recalculating reading definitions is expensive
$$RD \vdash S_1 \ \triangleright \ S_2  \ \triangleright  S_3  \ \triangleright \ \dots \ \triangleright S_n$$