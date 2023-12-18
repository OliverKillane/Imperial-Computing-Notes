## [Source](https://kowshik.github.io/JPregel/pregel_paper.pdf)

## Problem Statement
Graph algorithms have poor memory locality, small work per vertex (so high IO vs compute cost) and changing parallelism during execution 
- Graph based data is more common now than in the past (social media, web pages)
- Distribution over many machines increases the chance of failure.
- No general purpose, scalable system exists for implementing arbitrary graph algorithms over arbitrary graph representations.
## Data Model
$$S_i \underset{vertecies}{\longrightarrow} S_{i+1}$$
For each *superstep*, apply a user-defined function for each vertex in parallel.
```rust
/// if the vertex is active
fn (S: Superstep, V: vertex, M: message) -> bool {
	M.get(V); // get messages from S - 1
	let other: VertexID = V.some_conected_v();
	M.send(other); // send message to another V at S + 1 (can be any node with known identifier)
	
	// determine if active for the next superstep
	active
}
```
- Pregel programs are inherently deadlock & data race free, all communication is happening between *supersteps* 
- Edges have no associated computation.
- Vertices are *active* at the start, deactivate themselves until messaged by some other vertex.
- When all vertices vote to halt (no longer active) the algorithm terminates.
### Message Passing
Messages are delivered (no duplication, but also no order guarentee). 
1. No need for remote access for the algorithms to be used, message passing is sufficient
2. Latency of reads cannot easily be hidden, but message passing latency can be hidden/amortized by asynchronously delivering batches of messages.
The vertices and edges are stored on the machine doing the vertex's computation, machines only need to communicate messages. 

Some other optimisations include:
- `Combiners`, user defined functions for combining messages sent to a given $(S, V)$ to reduce network traffic.
### Aggregators
Each vertex in each step can provide a value to an aggregator, which are combined with a reduction operator.
- some are predefined (i.e. `min`, `max`, `sum`)
### Topology Changes
When there are conflicts, an arbitrary decision is chosen, unless the user specifies how to remove conflicts.
### Comparison With [[MapReduce]]
| [[MapReduce]] | [[Pregel]] |
|-|-|
| Entire State is transfered between machines | Vertecies and edges stay on the machines computing them, only transfer messages over network. |
| | |
### C++ API
```cpp
template class Vertex {
  public: 
	virtual void Compute(MessageIterator* msgs) = 0; 
	const string& vertex_id() const; 
	int64 superstep() const; 
	const VertexValue& GetValue(); 
	VertexValue* MutableValue(); 
	OutEdgeIterator GetOutEdgeIterator(); 
	void SendMessageTo(const string& dest_vertex, const MessageValue& message);
	void VoteToHalt(); 
};
```
## Lineage
- Inspired by [[Valiant’s Bulk Synchronous Parallel Model]]
## Architecture
### Setup
The user's program is compiled and downloaded to all the machines
- One of the copies is a *master* responsible for coordinating all the activity, the cluster's management system/name service is used to discover locations.
- *Master* determines the number of partitions, and assigns partitions to machines. Partitions determined by has (can be user provided)
- The data is loaded by workers (not related to their partitions), if they load data from a partition that is not theirs, they send it to the responsible worker.
- All vertices are marked as active, the master can now instruct workers to do supersteps (they respond with the number of active verticies at the end of each *superstep*)
- Messages are asynchronous, all delivered by end of the superstep.
- Once no vertices are active, the computation ends.
### Fault Tolerance
Checkpointing is used at the start of a superstep (for vertices, edges, any extra state & messages)
- Workers are pinged frequently to check if alive.
- On failure, reset back to checkpoints - can require lots of repetition.
- *Confined Recovery* where outgoing messages are logged, to allow only the failed node to require catch-up (it restarts from checkpoint with the messages from the healthy partitions). This requires determinism
