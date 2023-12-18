Need to be able to recover from inevitable failures (known rate over large scale)

| Method | Pros | Cons |
|-|-|-|
| Data redundancy | *Can* provide perfect recovery (potentially even live) | Significant cost of potentially fully redundant system, issues with consistency between main & replica  |
| Recovery | No cost of replication | Cost on failure, can be easy for  [[Stateless Services]] & stateless protocols, need to know operation order for compute jobs |  

Also need to consider types of failure:
- *Transient/temporary* failures - can simply wait to recover, serve data from elsewhere during change.
- *Permanent* failures - some disk is borked, and the data on it is irrecoverable.

[[Distributed Computing Properties]]