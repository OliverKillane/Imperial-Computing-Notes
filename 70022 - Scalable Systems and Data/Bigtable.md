## Data Model
Data is represented as a sparse, distributed, persistent, multidimensional sorted map.
- Indexed by `row: str`, `column: str`, `timestamp: int64` (timestamps can be assigned arbitrarily by clients)
- All values are an array of bytes (hence can use any data types, serialization needed by any application)
- Supports execution of client provided scripts (including by [Sawzall](https://en.wikipedia.org/wiki/Sawzall_(programming_language)) which is similar to [apache pig](https://en.wikipedia.org/wiki/Apache_Pig))
- Can be used with google's [[MapReduce]] 
### Rows
- `key: str` (up to 64KB)
- Read/write under a single row key is atomic (even for a large number of columns) (single row transactions only).
- Data kept in [[Lexicographical Order]] by row key. Each row range in a table is dynamically partitioned into [[Bigtable#Tablet|tablets]] (choosing a good key can create better locality as associated keys are stored together)
```python
key = "com.google.maps/index.html" # flipped domain to get better locality (maps pages stored together)
```

### Columns & Column Families
- Columns are grouped into *column families* which is the basic unit of access control. Disk and memory accounting are also decided at the column family level.
- All data in a column family is *usually* the same type.
- Can specify garbage collection for a column on older timestamps (e.g keep last $n$ entries)
```python
column_name = "family:qualifier" # must be printable, but are arbitrary strings

# e.g each webpage in a table has a language, language contains an ID column 
lang = "language:ID"
```
## Architecture
It is built upon the [[Distributed Filesystem]] [[Google File System]]/GFS (has since been replaced by [[Colossus]]).
### Tablet
The unit of distribution and load balancing.
- A range of rows from a table, 100-200MB in size
- Tablet Servers manage a set of tablets (10 to 1K), allocating new tablets, managing reads & writes, and splitting tablets that becomes too large.

$$\text{Chubby File} \to \text{Root Tablet (metadata)} \to \begin{matrix} \text{Other Metadata Tablet} \\ \text{Other Metadata Tablet} \\ \text{Other Metadata Tablet} \\ \dots \end{matrix} \to \begin{matrix} Table_a \\ Table_b \\ Table_c \\ \dots \end{matrix}$$
- $\text{Root Tablet}$ contains other tablet locations in a $\text{METADATA}$ table, is never split to ensure maximum hierarchy depth of $3$ levels
- Client library caches tablet locations to avoid re-lookup, only re-searching if the cached location is found to be incorrect
- Each [[Bigtable#Tablet|tablet]] is assigned to one server at a time, managed by the master. Synchronised with the tablet servers through [[Bigtable#Chubby|chubby]] using a servers directory of chubby files.

When a write occurs on a tablet server, after checking authorisation/access control by reading a chubby file of allowed writers, the write is sent to the tablet commit log.
- Commits can then be batched and the [[Bigtable#SSTable|SSTable files]] updated
- If data written is lost, a set of redo points (pointers to commit log entries) can be used to redo the write requests
- Compaction can occur (write memtable to SSTable, merge SSTables and memtable into one new SSTable and drop old)
### SSTable
A persistent, ordered, immutable map of `key: bytes` to `value: bytes` 
- Backed by a sequence of (configurable but typically 64KB) blocks with a block index (used to locate blocks) at the end of the file.
- Can use single-disk seek from an in memory index to get a block, or can even map the entire file to memory.
### Chubby
The chubby locking service is provides to ability to synchronise communication.
- Clients start sessions, users interact through a session
- Used in [[Bigtable]] to ensure there is only one master at a time, to organise/discover/kill [[Bigtable#Tablet|tablet]] servers. 
- Required for bigtable to run.
## Refinements
### Locality Groups
A group of multiple column families that are placed in an [[Bigtable#SSTable|SSTable]] to allow more efficient reads (reads may often only access one, or a few of the columns, do not need to access all).
- Can also specify locality groups to be lazily loaded into memory
### Compression
Each [[Bigtable#SSTable|SSTable]] block can be compressed separately by an algorithm of clients choice.
- No need to decompress entire file to read one block inside of it
- Two phase compression is often used (long strings, then repetitions in small window)
### Caching
Tablet servers have two caches
- *Scan Cache* is used for caching key-value pairs in[[Bigtable#SSTable|SSTable]]
- *Block Cache* for caching entire blocks read from GFS
### Bloom Filters
Clients can create a bloom filter for the [[Bigtable#SSTable|SSTables]] of a given locality group, and use this table to determine if a given row/column pair exists (to avoid looking up non-existent data on disk)

