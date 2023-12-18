## Problem Statement
[[MapReduce]] , [[Dryad]] and other compute distribution systems do not efficiently use memory.
- Many applications reuse results, but the aforementioned systems require data to be persisted to disk between operations.
- Existing in-memory systems (e.g. [[Piccolo]]) only allow data to be persisted by expensive replication across machines 
The aim of [[Spark]] is to use a new abstraction called [[Resilient Distributed Datasets]] to allow for such reuse.
## Data Model

transformations (e.g. `map`, `filter`) are combined into *actions* run on RDDs (e.g. `count`, `collect` and `save`).
- RDDs are computed lazily
- Users can `persist` data for use in future operations
- Users can specify alternative persistence strategies (e.g. replication, disk only etc)
- Users can set priority for persistence (if in-memory structures are too large)
### Language Interface
A language-integrated interface is provided (similar to [[Dryad#DryadLINQ]]).