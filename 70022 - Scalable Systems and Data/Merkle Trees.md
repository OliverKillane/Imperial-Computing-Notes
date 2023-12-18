A tree where each non-leaf node is a hash of its child nodes. It allows fast checking of when data has been changed.
```rust
enum Tree<T: Hash> {
	Leaf{pub data: T};
	Branch{ left: Box<Tree<T>>, hash: usize, right: Box<Tree<T>>}
}
```
- To check a subtree has been changed only requires comparing hashes.
- Hence each branch can be checked independently, and the entire tree does not need to be downloaded/in memory