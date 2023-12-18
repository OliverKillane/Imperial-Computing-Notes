## Data Model
Uses a subset of SQL to run 
## Design
An in-memory database, single threaded with transactions executed sequentially.
- no locking / latching
- uses replication for durability (*K-Safety*) instead of [[Write Ahead Logging]]
- Entirely in memory, so no need for buffer management.
- Partition data among a cluster of [[VoltDB]] nodes. Each partition operates independently an executes transactions serially.
It is built to *horizontally scale* - main memory is limited, need to spread across machines.
## Data Model
Each server contains several [[VoltDB]] partitions.
### Table Types
| Type | Description |
|-|-|
| Partitoned | A single column as partition key, rows spread across [[VoltDB]] partitions, use for data modified often |
| Replicated | All rows on every [[VoltDB]] partiton, used when modifications are infrequent |

Different workloads are supported:

| Type | Description |
|-|-|
| Single Partition | All insert/update/delete only occur in one partition so can compute on only one voltDB partition, on one server. The majority of work is like this |
| Multi-Partition | Occurs on replicated tables |
### Stored Procedures
Can create queries in java, have these analysed and stored with relevant [[VoltDB]] partitions.
- Better performance from optimising a known parameterized query.
- Can just invoke from application - no need to transfer entire query.
### Serializability
Each partition executes queries in order. This removes much of the complexity of managing  concurrent transactions, as well as the overhead from locking/latching.
- Throughput matters more than latency, so keeping high utilisation executing queries sequentially is fine.
### Migrations
Need to modify schema and the stored procedures, then build a catalogue and deploy it.
See here [Part 4: Schema Updates and Durability (voltdb.com)](https://docs.voltdb.com/tutorial/Part4.php).