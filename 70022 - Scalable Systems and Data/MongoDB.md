## Definition
A [[Document Database]] storing documents in [[BSON]] format.
- Uses [[BSON]] format to store documents, including with the 
- Documents use the `_id` field as a primary key in the collection of documents in a database. It is a unique, immutable, non-array type identity for the document. It can be considered the document's primary key int he collection of documents in a database.

| mongoDB | SQL |
|-|-|
| BSON Document | Tuple/Row |
| Collection | Table/View |
| `_id` field | Any attribute labelled as primary key |
| Schemaless | Schemafull |
| Embedding/Nesting | Joins |
Both can make use of indices to improve performance.
## [[CRUD]] Queries
See [db.collection.find() — MongoDB Manual](https://www.mongodb.com/docs/manual/reference/method/db.collection.find/#std-label-method-find-query) 
```js
// insert a document
db.<collection>.insert({<field> : <value>, ...})

// find all documents in a collection
db.<collection>.find(
	<query>,      // e.g. { _id : "london" }
	<projection>, // e.g. {  }
	<options>     // e.g. explain, limit: n
)

// UPDATE <collection> 
// SET <field2> = <value2> 
// WHERE <filed> = <value>
db.<collection>.update(
	{<field>:<value>}, 
	{$set : {<filed2> : <value2>}}, 
	{multi:true}
) 
```
## Data Model
Only actions in a single document are atomic (weak consistency).
### Embedding
For a 1-1 relationship, one document can be embedded in another.
```json
{
   _id: "Foo",
   bar : {
	   name: "bing",
	   status: "goat"
	}
}
```
We can also do this for 1-many using arrays.
### Linking
For 1-Many relationships we can just reference with the id.
```json
// alumni collection
{
   _id: "bob",
   age: 37,
   fav_colour: "green",
   school_id: "malmesbury"
}
```
```json
// schools collection
{
   _id: "malmesbury",
   ofsted: "outstanding"
}
```
### Indexes
Used to speedup queries by avoiding needing to can all documents in a collection.
- Single field, compound field and multikey indexes.
```js
db.users.ensureIndex({score: 1}) // sorted index on score ASC
db.users.getIndexes()
db.users.dropIndex({score: 1})

db.users.find(...).explain() // like explain in SQL

db.users.find().hint({score: 1}) // Override mongoDB choice, use the score ASC index

db.users.ensureIndex({userid: 1, score: -1}) // sorted index userid ASC, score DESC

// a multikey index, given each contains an array:
{
   _id: ...,
   addr: [
	   {zip: ...},
	   {zip: ...},
	   ...
   ]
}
// now each document has multiple keys in the index
db.users.ensureIndex( { addr.zip:1} )
```
### Aggregation
- Done on [[MongoDB]] so the application does not have to (reduce application complexity, and data needed to transmit over network).
```js
db.zips.aggregate(
	{$match : {country : "England"}},
	{$group : {_id : "England", population: {$sum : "$population"}}}
);
```
