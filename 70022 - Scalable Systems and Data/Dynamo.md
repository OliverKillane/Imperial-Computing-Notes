## Problem Statement
Needed an eventually consistent, always reliable database for Amazon shopping.
## Background
Dynamo is a distributed key-value store / primary key only database which is used by amazon for high reliability services.
- It uses object versioning, a quorum-like decentralised replica control protocol.
- Data is partitioned and replicated using [[Consistent Hashing]].
- Each service uses its own dynamo instances.
### Data Model
- Data is stored as binary objects, uniquely identified by a key.
- Unlike [[Bigtable]] there is no schema, it is just as simple as that: a key-value store
- No isolation provided, only operations on one key/value pair are atomic.

The paper argues that strong consistency & high availability are incompatible.
With dynamo a weaker consistency model is used.
- All data is eventually consistent.
- No data is made unavailable while resolving consistency issues.
- Resolving consistency issues can be done in a custom way, by applications (they have more knowledge about the semantics they want, than the dynamo, which should be data agnostic)

```rust
get(key);                 // Read data
put(key, context, object) // Commit data
```
## Architecture

| Properties | Description |
|-|-|
| *Incremetal Scalability* | Can scale out to more storage hosts / nodes, without impacting the operations of the system |
| *Symmetry* | Every node has the same responsibilities as peers (no controllers/masters) |
| *Decentralization* | Design favours peer-to-peer, no single points of failure |
| *Heterogeneity* | Use of different hardware, different levels of compute in nodes, work scaled on each node with ability |

| Problem | Technique | Advantage |
|-|-|-|
| Partitioning | [[Consistent Hashing]] allows reallocation of parts of a hashmap, without needing to reinsert all nodes| Incremental Scalability |
| High Availability for writes | [[Vector Clocks]] with reconciliation. | Version size is decoupled from update rates (I think this means not storing old versions, just the VC) |
| Handling temporary failures | Sloppy Quorum and hinted handoff | Availability higher than a stricter quorum requirement. |
| Recovery from permanent failures | Anti-entropy using [[Merkle Trees]] | Synchronizes divergent replicas in the background | 
| Membership and failure detection | Gossip-based membership protocol and failure detection | Preserves symmetry, no need for centralized store of node liveness and membership |
### Partitioning
$$hash(key) \to \text{lookup region on ring} \to \text{get node for the region} \to \text{operate on node}$$
Traditionally consistent hashing places nodes randomly on the ring, however for dynamo the *size* of the node needs to be considered.
- Each node has several virtual nodes (depending on node *size*)
- Randomly place virtual nodes on the ring
- Only nodes with virtual nodes adjacent to the virtual nodes of the failing node are affected by failure.
### Replication
Data is replicated on $n$ hosts (configured per-instance of dynamo).
- Each key is assigned a coordinator node that manages replication of data items
- There is a *preference list* of  coordinator nodes for a given key.
- Every node in the system can determine the preference list of a key.
### Data Versioning
Eventual consistency is provided, which allows updates to be propagated over time (asynchronously, hence under failure replicas may be updated much later).
- Each new write to the data is considered an entirely new immutable version of the data.
- A lineage of data is determined, when updates conflict it will attempt to reconcile using causality ([[Vector Clocks]]), and if not possible then the application gets both versions are reconciles them itself.
- [[Vector Clocks]] are used to capture causality between different versions of an object (used to determine if two versions are on parallel branches, or same branch in an order)
```python
def put(key, context, object):
	"""	
	1. coordinator generate new vector clock
	2. coordinator write new locally
	3. coordinator send update to the N highest-ranked reachable nodes
	4. If W - 1 respond, success
	"""
	

def get(key) -> object:
	"""
	1. coordinator requests all existing versions from N highest-ranked reachable nodes
	2. return all causally unrelated versions
	3. application reconciles and sends superceding version back
	"""
	pass
```

### Hinted Handoff
If some nodes are temporarily down, a `put(...)`  may fail after not getting the required quorum.
- Can temporarily hold updates, until enough nodes are reachable to attempt a quorum
- Write be handed off to a node it would not normally *reside* on,  once reconnected and replicated to the intended node the temporary copy can be removed, replica count remains the same.

### Replica Synchronization / Anti-entropy
Nodes need to stay synchronized to prevent data being lost when a node permanently fails.
- Each node has a [[Merkle Trees|merkle tree]] of each key range (virtual node on [[Consistent Hashing]] ring covers a key), nodes share the root of their tree, and a difference in the root hash means a difference in data.
- Can then start getting hashes of different nodes in the tree (efficiently, does not need entire tree) to determine which data needs to be synchronized 

## Implementation
## Components
### Request Coordination
### Membership
### Failure Detection
### Persistence Engine
- can use many different engines (MySQL, DBD Java, in memory buffer with persistent store)
- Application chooses the engine to be used.
