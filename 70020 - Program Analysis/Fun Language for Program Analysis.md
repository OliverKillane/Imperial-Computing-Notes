## Syntax
$$\begin{matrix*}[l l l] 
e & \in \mathbf{Exp} & \text{Expressions/Labelled Terms} \\
t & \in \mathbf{Term} & \text{Terms/Unlabelled Expressions} \\
\end{matrix*}$$
With the syntax
$$\begin{matrix*}[l l r l l] 
e & ::= && t^\ell \\
t & ::= && c & \text{Constant } \in Bool \cup \mathbb{N} \text{ etc}\\
&& | & x & \text{Variable} \\
&& | & \mathbf{fn} \ x \Rightarrow e_0 & \text{Function} \\
&& | & e_1 \ e_2 & \text{Applying one term to another} \\
&& | & \mathbf{if} \ e_0 \ \mathbf{then} \ e_1 \ \mathbf{else} \ e_2 \\
&& | & e_1 \ op \ e_2 & \text{Operations include } \land, \lor, , -, *, \text{ etc} \\
&& | & \mathbf{let} \ x = e_1 \ \mathbf{in} \ e_2 \\
\end{matrix*}$$
## Concrete Domain
$$\begin{matrix*} 
\rho \in \mathbf{Env} & = \mathbf{Var} \mapsto \mathbf{Value} \\
v \in \mathbf{Value} & = \mathbf{Constant} \cup \mathbf{Closure} \\
\mathbf{Closure} &::= \left[ (\mathbf{fn} \ x \Rightarrow e_0), \rho \right]
\end{matrix*}$$
- The environment is like the [[Variable Store]], but expanded to include [[Closures]]
- Closure's capture from their environment, and hence need to contain an environment. 
## Evaluation
$$eval(\rho, e) = v \qquad e \text{ evaluates to } v \text{ in environment } \rho$$
- Here $eval$ is a [[Fun Language for Program Analysis]] interpreter
### Basic Rules
$$\begin{matrix*}[r l l l l l] 
eval( &\rho,& c^\ell & ) = & c \\
eval( &\rho,& x^\ell & ) = & \rho(x) \\
eval( &\rho,& (t_1^{\ell_1} \ op \ t_2^{\ell_2})& ) = & eval(\rho(t_1^{\ell_1})) \ op \ eval(\rho, t_2^{\ell_2}) \\
\end{matrix*}$$
### Selection
$$eval(\rho, \ (\mathbf{if} \ t_0^{\ell_0} \ \mathbf{then} \ t_1^{\ell_1} \mathbf{else} t_2^{\ell_2})^\ell) = \begin{cases} 
eval(\rho, t_1^{\ell_1}) & if \ eval(\rho, t_0^{\ell_0}) = true \\
eval(\rho, t_2^{\ell_2}) & if \ eval(\rho, t_0^{\ell_0}) = false \\
\end{cases}$$
- Note that we are not statically typing this, we could return any expressions from either side.
### Closure Creation
$$eval(\rho, \ (\mathbf{fn}\ x  \Rightarrow e_0)^\ell) = \left[(\mathbf{fn} \ x \Rightarrow e_0), \ \rho\right]$$
evaluating a closure requires saving the current environment as a capture.
### Let
$$eval(\rho, \ (\mathbf{let} \ x = t_1^{\ell_1} \ \mathbf{in} \ t_2^{\ell_2} )^\ell) = eval(\rho[x \mapsto eval(\rho, \ t_1^{\ell_1})], \  t_2^{\ell_2})$$
- Note that we shadow any variable currently available. (e.g. $\mathbf{let} \ x = 1 \ \mathbf{in} \ (\mathbf{let} \ x = 2 \ \mathbf{in} \ x)$ )
### Function Application
$$eval\left(\rho, \ (t_1^{\ell_1}, \ t_2^{\ell_2})\right) = eval\left(  \rho_0[x\mapsto v_2], \ e_0 \right)$$
$$\text{where } \qquad \begin{split}
eval( \rho, \ t_1^{\ell_1}) & = [(\mathbf{fn} \ x \Rightarrow e_0), \ \rho_0] \land \\
eval(\rho, \ t_2^{\ell_2}) & = v_2 \\
\end{split}$$