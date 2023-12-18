## Data intensive Applications
50%-80% of CPU cycles are stalls due to *instruction fetch* (capacity misses) and *data fetch* (compulsary misses).
- Need to maximise locality and cache line utilisation for data.
### Prefetching
Simple next-line fetching is good for sequential access, but does not work for instructions (not sequential. control flow), or non sequential access (e.g. traversing structures through pointers).
- *Temporal Streaming* is where the history of accesses is used to determine which lines to pre-fetch. Hence for repeated control flow accessing the same (non-sequential) blocks of memory we get some speedup. But need to record this history (space cost).
- *Software Guided Prefetching* to prefetch the blocks likely to be accessed (e.g child nodes of a tree).
### Cache-Conscious Code
Includes reducing the code/text size to reduce capacity misses in the instruction cache, or with regards to code layout:
- minimising jumps to help the next-line fetcher
- avoiding associativity conflicts in instructions used together (e.g. mutually recursive functions that map to the same cache lines)
- profile guided optimisation
- Just-in-time compilation
- compiling queries to machine code (optimise to reduce size)
### Cache-Conscious Data
To increase utilisation and make the next-line prefetcher effective
- row stores good for [[OLTP]] (few rows, many columns)
- column stores good for [[OLAP]] (lots of rows, few columns)
- Aligning data to line size to reduce lines needed to access some data, but without adding so much waste that this reduces utilisation.
- consider access patterns for data structures (e.g. scanning a tree, versus traversing)

| Operators | Effect |
|-|-|
| Volcano | Poor instruction locality (calls pass up the query graph) and data locality |
| Vectorized/Bulk | Better instruction locality, better data locality, easier to exploit SIMD cost of copying data |
### Computation Spreading
Keeping transactions that use the same data / instructions on the same core.
- e.g. schedule threads on a core, based on what they need to access, if a core already has those instruction/data in cache (e.g. just executed a similar query), then can just schedule there.
- Helps with the core-specific resources (e.g. level 1 data and instruction caches)
## Multithreading Limitations
We can use more threads, running on more cores to speedup computation, however as the number of threads increase, performance plateaus:
- [[OLTP]]  bounded by the access latency of the table.
- [[OLAP]] bounded by memory bandwidth
We also have the issue of contention. Lots of random accesses to data synchronised by locks and [[Latches]].
## Synchronisation
Contention in critical sections is bad.
- *Unbounded* where any number of threads could be waiting for a resource (bad)
- *Fixed* a fixed number of threads need some critical section. (Good)
- *Cooperative* Using logging, an access order is determined. (Good)
*Cooperative* only needs logging (e.g. [[Write Ahead Logging]]), others need a lock manager. For locks, [[Speculative Lock Inheritance]] can be used.

[[In Memory Databases]] reduce this requirement:
- Do not need to wait as for disk, so executing queries serially can give acceptable performance.
- Executing serially removes locking overhead.
## Hardware Islands
Multiple cores on a CPU, multiple CPUs in a system, multiple systems in a cluster.
- On a multi-socket system, we have a [[Non Uniform Access Model]], sharing data between sockets results in excess latency.
- On a single core, sharing data (rather than message passing) can be more efficient.
- Need to decide how *hardware islands* are defined, no sharing between islands, sharing inside an island.
- Sharing requires [[Databases Performance#Synchronisation|synchronisation]].
- Partitioning data between non-sharing requires the cost of repartitioning.
