## Definition
Extensible-markup language designed to hold semi-structured tree-based data.
- Parent nodes have tags, attributes and children. Children are ordered.
- Can be described/typed/structure checked using some specification, for example [[XSD]], or [[DTD]]
- Open standard, very extensible (e.g. for data, configuration, making embedded DSLs), human readable.
- Popularity means much tooling is available.
```xml
<?xml version='1.0' encoding='UTF-8'?>
<Config>
  <Date>31/02/2023</Date>
  <NumberOfCores>48</NumberOfCores>
  <Codes>
    <Int>101</Int>
    <Int>345</Int>
    <Int>42</Int>
    <Int>67</Int>
  </Codes>
  <ShowLogs>false</ShowLogs>
</Config>
```
## Storage
Typically just text, stored in files (e.g. application configuration)
- Can use an object oriented database (e.g. excelon), or Tamino
Two approaches are used for mapping xml data into a database.
### Structure Mapping
Using some structure description (e.g. [[DTD]]) to get the structure of documents.
### Model Mapping
No structure information is required for storage, and a fixed, generalised schema is used for all xml documents.
- Can support applications changing structure over time
- Can support [[XML|xmls]] that are not well formed, e.g. with no [[DTD]]
- Less complex user setup and database implementation from being generalised.
We will use the example:
```xml
<parent>
	<child1> bob </child1>
	<child2> 
		<grandchild> jim </grandchild>
	</child2>
</parent>
```
#### Edge Approach
$$\text{Edge}(\text{Source Node}, \ \text{Target Node}, \ \text{Label/Name}, \ \text{Flag}, \ \text{Value})$$
- $\text{Flag}$ is either `ref` or `val` depending on if it is a leaf node with a value, or just an edge connecting some parent and child.
$$
\begin{matrix*}[l | l | l | l | l]
\text{Source Node}&  \text{Target Node}&  \text{Label/Name} & \text{Flag}& \text{Value} \\
\hline
\&0 & \&1 & \text{"parent"} & ref & - \\
\&1 & \&2 & \text{"child1"} & val & \text{"bob"} \\
\&1 & \&3 & \text{"child2"} &ref & - \\
\&3 & \& 4 & \text{"grandchild"} & val & \text{"jim"} \\
\end{matrix*}
$$
#### Monet Approach
Store Each label path as a table. with each as $\langle node, \ value / ref, \ position/ordinal \rangle$.
$$
\begin{split} 
parent \to child1 &= [ \ \langle \&2, \ \text{"bob"}, \ 1 \rangle \ ] \\
parent \to child2 &= [ \ \langle \&3 , \&4, 1 \rangle \ ] \\
parent \to child2 \to grandchild &= [ \ \langle \&4, \ \text{"jim"}, \ 1 \rangle \ ] \\
\end{split}
$$
#### XRel Approach
A node based approach using four tables:

| Table | Attributes | Purpose |
|-|-|-|
| Path | $(PathID, PathExp)$ | Maps path identifiers to an actual path, e.g. $2 \mapsto \#/parent/child2/grandchild$  |
| Element | $(PathID, Start, End, Ordinal)$ | Contains the start and end of a region (positions of the start & end tags in xml), as well as the ordinal of the region in its parent. |
| Text | $(PathID, Start, End, Value)$ | The value for a region, e.g. it is a text element |
| Attribute | $(PathID, Start, End, Value)$ | Contains the attribute value for a path (element name) |
#### XParent Approach
A path based approach using four tables:

| Table | Attributes | Purpose |
|-|-|-|
| LabelPath | $(ID, Len, Path)$ | Contains each path's ID, e.g. $1 \mapsto (3, \ ./parent/child2/grandchild)$ |
| DataPath | $(Pid, Cid)$ | Maps path IDs |
| Element | $(PathID, Ordinal, Did)$ | At some path, some node has some data identifier |
| Data | $(PathID, Did, Ordinal, Value)$ | Some path, data identifier, ordinal has some value (text) |
#### Comparison
- XRel and XParent outperform Edge for complex queries. 
- Simple queries, Edge can sometimes be better. 
- Label Paths reduce the querying time.