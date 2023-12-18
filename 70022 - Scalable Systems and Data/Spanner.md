## Motivation
[[Bigtable]] does not work for applications that need large, complex & changing schemas, or that require strong consistency ([[Bigtable]] provides atomicity only per row update).

Spanner is designed to support a SQL-like language with transactions, distributed across multiple datacentres. 
- Applications can control replication (e.g number of replicas, read-latency)
- Consistent reads & writes (including externally consistent reads and writes)

TODO: externally vs globally consistent - What does this mean?
## Data Model
A SQL-like relational model.
- Transactions have a timestamp, and are applied globally in a linearizable order
- Can integrate with [[MapReduce]]

Each spanner universe contains several databases, containing an unlimited number of schematized tables.
- Every table needs to have an ordered set of one-or-more primary columns (the row-key)
- Uses [[Two-Phase Commit]]

Uses two-phase locking to allow long running transactions to be efficient (rather than constantly failing as with optimistic).

| Operation | Concurrency Control | Replica Required |
|-|-|-|
|read-Write Transaction | Pessimistic | Leader |
| Read-Only Transaction | Lock-free | leader for timestamp, any for read |
| Snapshot read, client timestamp | lock-free | any |
| Snapshot read, client bound | lock free | any |
## Architecture
Each spanner deployment is called a *universe*, organised into [[Spanner#Zones|zones]] (analoguous to a [[Bigtable]] deployment).
### Zones
![[spanner_hierarchy.png]]
- Zones are the unit of administrative deployment, can create/remove new zones
- A datacentre may have multiple zones
- *Location proxies* are used by clients to locate *spanservers*.

### Tablets
Similar to [[Bigtable#Tablet|bigtable tablets]] they implement a mapping:
$$(key: str, timestamp: int64) \to str$$
- Unlike [[Bigtable]] spanner assigns timestamps itself.
- State is stored using btree-like-files with [[Write Ahead Logging]]
- [[Colossus]] (successor to the [[Google File System]]) is used for files.

### Directories
Tablets contain a number of directories (unlike [[Bigtable#Tablet|bigtable tablets]] which store a section of contiguous rows).
- Directories are just buckets
- Can be transferred around while the client operations are still occurring 
### Replicas
![[spanner_groups.png]]
Each replica uses a [[Paxos]] state machine to get consensus on a transaction log and metadata.
- Some replicas are *long-lived leaders* which also manage the currently held locks and currently running transactions.

### TrueTime
```rust
mod TT {
	type Timestamp = i64;
	
	pub fn now() -> (Timestamp, Timestamp) { 
		// ...
		(earliest, latest)
	}

	pub fn after(ts: Timestamp) -> bool {
		let (_, latest) = now();
		latest < ts // definitely passed
	}

	pub fn before(ts: Timestamp) -> bool {
		let (earliest, _) = now();
		ts < earliest // definitely before
	}
}
```
- Uses multiple time references (GPS, atomic clock)
- Single *time master* machine per datacentre, and *timeslave daemon* per machine.
# TODO: Up to TrueTime
