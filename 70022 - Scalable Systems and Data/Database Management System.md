## Definition
## Storage Layer
Includes buffer & disk space management.
- the operating system can provide a file abstraction, however this hides details the DBMS may need or want (for performance) to manage.

DBMS conflicts with the OS on:
- Need for specialized prefetching
- Control over the buffer replacement policy (e.g LRU)
- Control over thread/process scheduling ([[Convoy Problem]])
- Control over persistence/when data is flushed/committed to disk (e.g log entries to disk before queries in [[Write Ahead Logging]])
### Disk Storage
Random access slower than sequential access.
- access to blocks takes delay to rotate to block.
See [[Hard Disk Drive]].
### In-Memory
- Very expensive and must also deal with DRAM volatility.
- Improved performance due to lower access latency
- Volatility can be fine for some applications, so is used (e.g [[Redis]] cache)