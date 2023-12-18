## Definition
We can define [[Live Variable Analysis]] using set constraints as:
$$LV_{exit}(\ell) \supseteq \begin{cases} 
\emptyset & \mathbf{if} \ \ell \in final(S_*) \\
\bigcup\{LV_{entry}(\ell') \ | \ (\ell', \ell) \in flow^R(S_*)\} & otherwise \\
\end{cases}$$
$$LV_{entry}(\ell) \supseteq (LV_{exit}(\ell) \setminus kill_{LV}([B]^\ell) \cup gen_{LV}([B]^\ell)) \ where \ [B]^\ell \in blocks(S_*)$$
- We can prove given a [[Label Consistency|label consistent]] program $S_*$ $live \vDash LV^=(S_*) \Longrightarrow live \vDash LV^\subseteq(S_*)$ - that the least solution for both coincide.