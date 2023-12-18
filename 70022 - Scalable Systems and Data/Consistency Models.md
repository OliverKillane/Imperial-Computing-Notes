We can use consensus algorithms to replicated data remains consistent across distributed read/writes (e.g [[Paxos]], raft).
- Consensus algorithms typically expensive (network)
- To improve performance, we can reduce the consistency guarantees. (Not all systems need perfect consistency)
- Not all services within an application even need the same consistency level (e.g account balance for bank, vs order of new posts on social media)
### Examples
- [[Dynamo]] and [[Bigtable]] weaken consistency (only offer single row/object transactions) for better availability, scalability & performance.
- [[Spanner]] introduces some complexity to manage strong consistency at a given point in time


[[Distributed Computing Properties]]