## Definition
A declarative, pattern matching graph querying language.
- Can be used with [[Neo4j]]
- Documentation can be found at [Core concepts - Cypher Manual (neo4j.com)](https://neo4j.com/docs/cypher-manual/current/queries/concepts/)
## Examples
### Basic Queries
```cypher
// query over all nodes
START n=node(*) 
WHERE has(n.name) AND n.name = "Tom Hanks" 
RETURN n;
```
```cypher
// create a node
CREATE ({title:"Mystic River", released:1993});
```
```cypher
// add properties
START a=node(*) 
MATCH (a) 
WHERE a.title = “Mystic River” 
SET movie.released = 2003 
RETURN movie;
```
```cypher
// add relationships
CREATE UNIQUE (kevin)-[:ACTED_IN {roles:["Sean"]}]->(movie) 
WHERE movie.title = “Mystic River” 
	AND kevin.name = “Kevin Bacon”
```
```cypher
// delete nodes and relationships
MATCH (emil)-[r]->() 
WHERE emil.name = “Emil Eifrem” 
DELETE r, emil;
```
### Complex Queries
```cypher
MATCH (gene)-[:ACTED_IN]->(movie)<-[:ACTED_IN]-(n)
WHERE (n)-[:DIRECTED]->() AND gene.name = ”Gene Hackman” 
RETURN DISTINCT n.name;

MATCH (keanu)-[:ACTED_IN]->(movie)<-[:ACTED_IN]-(n) 
WHERE NOT((hugo)-[:ACTED_IN]->(movie)) 
	AND keanu.name = “Keanu Reeves” 
	AND hugo.name = “Hugo Weaver” 
RETURN DISTINCT n.name;

MATCH (actor)-[r:ACTED_IN]->(movie)
WHERE "Neo" IN r.roles 
	AND actor.name = “Keanu Reeves” 
RETURN DISTINCT movie.title;

// matching multiple relationships
START a=node(*) 
MATCH (a)-[:ACTED_IN|DIRECTED]->()<- [:ACTED_IN|DIRECTED]-(b) 
CREATE UNIQUE (a)-[:KNOWS]->(b);

// variable length paths (here length 2)
MATCH (keanu)-[:KNOWS*2]->(fof) 
WHERE keanu.name = “Keanu Reeves” 
RETURN DISTINCT fof.name
```