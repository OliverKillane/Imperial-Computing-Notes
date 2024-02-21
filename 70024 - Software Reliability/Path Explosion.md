## Definition
Real world programs contain many conditions resulting in a huge number of (often exponential in terms of conditions) paths.
- When using [[Symbolic Execution 1]]to find bugs, we should prioritise the most important paths
## Solutions
### Search Heuristics

#### Depth First Search
Only need to keep one active state (the current), can potentially miss out on other important code paths (when using time limit) by going exhaustively through one large path.
#### Breadth First Search
Need to keep many states of incomplete paths in memory.
#### Best-First Heuristic
Used by [[EXE]]. In [[EXE]] each fork is run as a separate process, it chooses the *best-first candidate* as the suspended process on the line executed the fewest number of times.
The *best-first candidate* is then executed as depth-first for some time, before making the *best-first candidate* selection again.

This avoids exploding paths in loops (those instructions are run many times, and hence de-prioritised as *best-first candidates*).
#### MD2U
Available in [[KLEE]]
$$MD2U(s) = \min\left(\text{distance from s} \to \text{uncovered instruction} \right)$$
States are selected according to weight $\cfrac{1}{MD2U(s)^2}$ to prioritise sattes close to uncovered instructions.
#### Random Path
Given an execution tree, assuming each subtree has an equal probability of hitting uncovered code (size not considered).
- Each tree's weighting of being chosen is based on the depth (e.g. higher has larger weighting)
- for depth $n$ of binary tree $weight(n) = 2^{-n}$
This helps avoid starvation, we can never get stuck choosing the same path due to random nature of path selection.
#### Round Robin
Can take multiple heuristics and apply them in a round robin fashion.
### Eliminating redundant Paths
- If two paths reach the same [[Program Point]] with the same set of constraints, we can merge the states / prune one path.
- We can discard constraints for memory that is never read again (e.g. freed, destroyed at end of scope)
The basic algorithm is as follows:
```python

# The set of reduced Path Conditions visited before by Program Point P
cache_set: dict[ProgramPoint, set[PathCond]] = ...

# Locations read from P when reached with PC
read_set: dict[tuple[ProgramPoint, PathCond], set[Location]] = ...
trans_cl: dict[tuple[PathCond, ReadSet], Constraint] = ...

# when program point p reached with path condition pc
def reachedwith(p: ProgramPoint, path_cond: PathCond) -> None:	
	for pc in cache_set[p]:
		# If the conditions involving this path and the read set at 
		# this point overlap with all path conds in the cache set
		if trans_cl[(path_cond, read_set[p, path_cond])] == pc
			halt_exploration()
		
		# get the read locations at this program point and path_cond 
		read_set[p] = compute_read_set(p, path_cond)
		# update the path conditions at this point 
		cache_set[p] = cache_set[p].union(
			trans_cl[path_cond, read_set[p, path_cond]] 
		)
```
### Statically Merging Paths
Converting branching into an expression.
```rust
let x: i32;
if c {
	x = A();
} else {
	x = B();
}
```
Can be converted to:
```rust
let x: i32 = if c { A() } else { B() }; 
```
This is called *phi-node folding* , the expression must be side-affect less.
- There is no overhead runtime overhead (single path)
### Test-Suite-Based Prioritisation
Many applications already have large test suites.
- Designed by developers to test features important to them / prioritised
- Typically have good coverage
- Often missing corner cases / cases not considered by developers
These test suites can be used to guide the tool, and prioritise which paths to check first.

For example [ZESTI](https://www.doc.ic.ac.uk/~cristic/papers/zesti-icse-12.pdf) uses an existing regression suite to determine which paths are interesting.