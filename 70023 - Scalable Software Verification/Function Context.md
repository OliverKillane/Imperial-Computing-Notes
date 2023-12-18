## Definition
$$\gamma_1, \gamma_2, \gamma_3, \dots \text{range over by } \ FContext \triangleq FName \rightharpoonup_{fin} List(Var) \times Cmd \times Exp$$
- A list of parameters as $List(Var)$
- Some commands for the function $Cmd$
- The return expression $Exp$
- Local variables are initialised as $null$ 
$$\gamma(f) = (\overrightarrow{x}, (C, E)) \ \text{ for example } \ \gamma(foo) = (a:b:c:\epsilon, (x := new(a + b + c), x))$$