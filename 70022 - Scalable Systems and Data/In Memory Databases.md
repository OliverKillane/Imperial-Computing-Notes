## Definition
By keeping all data in memory, we can avoid major sources of work:
- Management of the buffer pool (*its all in memory anyway*)
- Recovery / disk persistence (*no disk*)
- Locking + [[Latching]] & (typical) transaction implementation (*Less need to hide the latency memory compared to disk, so can execute queries sequentially*)
## Alternatives
### OldSQL
Legacy databases, designed around SQL & disk usage.
- Often optimised for benchmarks as sales is a large priority.
### NoSQL
Given up on ACID, transactions, and use a different data model.
- Typically weaker consistency
- Can design data model for specific application usage
### NewSQL
Keep ACID and an interface with SQL semantics, change the underlying design to improve performance
- [[VoltDB]], [[AlloyDB]], [[Spanner]]
