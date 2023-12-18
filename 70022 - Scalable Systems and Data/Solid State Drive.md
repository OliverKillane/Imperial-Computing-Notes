## Definition
Non-volatile storage using MOS transistors to trap charge.
 Often used in combination with *disks* as a cache/intermediate layer.
## Data Model
- Blocks (random access, unlike sequential for [[Hard Disk Drive]]).
- Can only write an entire block, so updates require reading elsewhere, editing and writing the entire block back.
- Efficient random reads, random writes less efficient.
## Hardware
Contains a controller, and several dies containing blocks of flash, containing the pages.
- Low endurance, blocks die after a number of cycles (erase/flash), which reduces drive capacity.
### Flash Transition Layer
A complex device driver/firmware.
- Used to manage performance and the lifetime of the device (blocks have a maximum number of writes before they are degraded / marked as unusable)
## Usage in DBMS
### Append & Pack
Can write a log sequentially instead of doing in-place updates.
- once a page is invalidated, it is marked as such as later reclaimed when data is *packed*
- reduces uneven wear (more even number of writes per block)
- Natural pattern for [[Write Ahead Logging]]
### Flash-Only [[OLTP]]
As [[OLTP]] is dominated by random reads/writes which are faster on flash, we can keep this DB on flash.
- The working set of records can fit on smaller flash device.
- Can even just keep [[Write Ahead Logging|write ahead log]] on the SSD and keep the OLTP database in memory.
### Flash Aided Business Intelligence
Scattered updates and large read only queries (e.g. scan over most data for analysis).
- Can speed up in-place updates (can batch them)
- Like delta-main: write updates to flash, flush to disk periodically, merge when queried to get some of the advantages of flash. Merge cost insignificant compared to disk access.
### Materialised Sort-Merge
*From [sigmod135-athanassoulis.dvi (bu.edu)](https://cs-people.bu.edu/mathan/publications/sigmod11-athanassoulis.pdf)*.  Writing updates to SSD, and efficiently merging results queried from the SSDs and disk. Migrations shift some data from SSD to disk.