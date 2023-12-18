## Definition
Systems for storing large volumes in infrequently accessed data.
- Include archival data (e.g. data stored for regulatory purposes that is rarely accessed for business needs)
- Needs very high capacity, cheaply.
- Cost is important - the data is infrequently accessed, so unlikely to contribute nto company profit
- Access can be very slow
For a *Write Once - Read Occasionally*/WORO workload. 
## Provisioning
Often using very cheap disks (e.g. [[Shingled Magnetic Recording]]), or magnetic tape, or even blu-ray disk.
We only need the minimum resources required for the write & rare read workload.
- Only need power, cooling required for the small read workload (not for massive access)
- Bandwidth can also be small (we do not care about slow access)
- Only need disks to be on during access.
## Architecture
A CSD rack with groups of disks, at any time one group can be spun up.
- switching group on order of $10\to30$ seconds.
- Need to track placement of data
- Random access is **very** slow
## Examples
### Microsoft Pelican
A 52U rack with 1152 archival class $3.5$ inch SATA disks each with avg $4.55$ TB storage for total $5$ PBs of storage.
- Only 8% of disks are active at a given time.
Systems on board (domains) supply resources (power, cooling, bandwidth) to a subset of disks.

| | |
|-|-|
| Domain-Conflicting | Disks that are in the same resource domain |
| Domain Disjoint | Disks with no shared resources |
- Disjoin can be simultaneously active, conflicting potentially cannot.
- Disks are split into groups (all disks in a group can be concurrently active / are disjoint), each blob/file is split into $k$ $128$KB fragments 
- I/O scheduler can reorder operations to amortize the spinup latency of groups.
#### Advantages
- reduced costs & power consumption
#### Disadvantages
- Tight constraints
- No thorough justification published by Microsoft / maybe not optimal?
- Sensitive to hardware changes
### Others
- OpenVault's Knox
- Facebook Cold storage
- Amazon Glacier
## Data Processing
### Load
When querying data, software needs to batch requests and cache to reduce the number of expensive group switches.
### Store
Data must be flushed back to the [[Cold Storage]] once the buffer is full, while reducing the number of group switches.

| Method | Description |
|-|-|
| Buff-Pack | (Greedy Algorithm) Flush to current disk group, then switch to disk group with most free capacity |
| Off-Pack | Flush the entire buffer to disk, can write to any disk group, then transfer later. |
*Off-Pack* is better for smaller buffers, higher number of disk groups and for higher throughput.
- Terminology from [this paper](https://hardbd-active.github.io/2018/papers/HadianH-hardbd-active-18.pdf).