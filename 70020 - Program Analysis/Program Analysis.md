### Definition
An automated technique for determining properties of programs without executing them.
- Used for compiler optimisations (e.g [[Available Expressions]])
- Program verification/correctness
- Security Analysis (e.g eBPF restricted C)

Program analysis should be *unambiguously specified*, *computable* and *correct*.
### Safe Approximations
In avoiding the [[Decidablility]] problem we can approximate
- *yes* (known to be true)
- *no* (not true, or unknown)
### Parity Example
We want to analyse the following program for the statement: 
$$\text{The program always returns an even m, for all values of m and n}$$
```rust
fn factorial_times_2(n: usize) -> usize {
	let mut m = 2; 
	while n > 1 {  
		m *= n;    
		n -= 1;
	}
	m
} 
```
We want to determine the parity of the attaching a tag for the parity to each [[Program Point]].
$$m_{tag} \in \{Even, Odd, Unknown\}$$
We can then propagate these, an see $m$ stabilise on $Even$.

[[Data Flow Analysis]] 