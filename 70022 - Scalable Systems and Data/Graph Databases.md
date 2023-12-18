## Definition
Databases organising data as nodes connected by relationships.
- As generally applicable as relational databases.
- Each to query and reason about (e.g. getting neighbour nodes vs joins).
- Scales well, but eventually needs to be sharded/partitioned across machines (active research area).

| Graph Type | Description |
|-|-|
| Undirected | $-$ |
| Directed graph | $-$ |
| Multigraph/Pesudograph | Can have multiple arcs between the same nodes. |
| Hypergraph | Single arc can connect more than 2 nodes |
Graph arcs can contain information, for example:
- weighted graphs (e.g. for pathfinding)
- labelled graphs (e.g. $person \to_{has} item$ $person \to_{parent} person$)
- Property graphs (e.g. purchase details)
## Implementations
Needs to provide an interface for easy querying (e.g. [[Cypher]]).
- Indexes for fast lookups
- Even as the graph size increases, the cost of traversing a single arc should remain constant (when modelling graphs in a relational database with an edges table, this is not true)

Graph databases include [[Neo4j]]