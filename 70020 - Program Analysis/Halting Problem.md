There is no algorithm that can determine in finite time if any program terminates.

### Fermat's Last Theorem
$$\neg \exists a,b,c, n . \ [ n > 2 \Rightarrow a^n + b^n = c^n ]$$
We can specialise for $n=3$ as:
```rust 
fn fermat(n: i32) {
	let mut try = true;
	let mut x = 1;
	while try {
		let mut y = 1;
		while y <= x && try {
			let mut z = 1;
			while z <= y && try {
				try = x.pow(n) + y.pow(n) != z;
				z += 1; 
			}
			y += 1;
		}
		x += 1;
	}
	unreachable!("This is never reached as per Wiles' proof")
}
```

### Collatz Conjecture
Termination is not yet proven for all positive integers. 
$$fn(n) = \begin{cases} f(n/2) & if \ n \equiv 0 \mod 2 \\ f(3n+1) & if \ n \equiv 1 \mod 2\end{cases}$$
```rust
// technically should use arbitrary size integer
fn collatz(x: usize) {
	if x % 2 == 0 {
		collatz(x/2)
	} else {
		collatz(3*x + 1)
	}
}
```
