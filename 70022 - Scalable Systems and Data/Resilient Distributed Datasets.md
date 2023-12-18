## Definition
> RDDs are fault-tolerant, parallel data structures that let users explicitly persist intermediate results in memory, control their partitioning to optimize data placement, and manipulate them using a rich set of operator
> [Spark paper]
- Enables efficient data reuse & hence allow for efficient iterative algorithms
- Coarse-grained transformations are applied with persisted logging to enable the data to be recomputed (hence fault-tolerant).  
## Usage
Best suited to `map`s over a large dataset (simple lineage, small commit log)
- unsuited to fine grained shared state (large commit log)
## Comparison with Distributed shared memory

| **Aspect** | **RDDs** | **DSM** |
|-|-|-|
| Reads | Coarse- or fine-grained |  Fine-grained |
| Writes | Coarse-grained | Fine-grained |
| Consistency | Trivial | Up to app/runtime |
| Fault Recovery | Fine grained & low overhead using lineage (can reproduce from operators) | Checkpoints and program rollback |
| Straggler Mitigation | Possible using backup tasks | Difficult |
| Work Placement | automatic based on data locality | Up to app (runtimes try to be transparent) |
| Out of memory | Same as existing flow systems | Poor performance due to swap |
