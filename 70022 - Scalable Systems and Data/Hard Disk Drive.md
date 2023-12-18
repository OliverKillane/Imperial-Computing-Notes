
## Definition
The most popular secondary storage choice encoding information using a magnetic disk.
## Data Model
Data stored in units of blocks/pages. 
- Sequential access $10 \times$ faster than random.
- $1000 \times$ slower than main memory ([[DRAM]])
- Align data page/block size for best performance
## Hardware
Contains a stack of platters containing the data, a write head can sweep across tracks (concentric circles) on the disk to read data from them.
- Multiple heads, but only one read/writes at a time.
- A *cylinder* is the same tracks on all the platters.
- Some disks have *zones* (can fit more data on outer tracks)
- A sector is a segment of the platter, *sector size* is a multiple of *block size*.
New disks also make use of [[Heat-Assisted Magnetic Recording]]
$$\text{access time} = \underbrace{\text{seek time (1-20ms)}}_{\text{move arms to track}} + \underbrace{\text{rotational delay (0-10ms)}}_{\text{Wait for disk to rotate}} + \underbrace{\text{transfer time (<1ms per 4KB page)}}_{\text{To read/write}}$$
- *settle time* is part of *seek time* (is roughly constant) the time taken to switch to an adjacent track (small distance), hence short seeks are dominated by *settle-time*
## *Next* Block Concept
$$(\text{Closest}) \qquad \text{Same Track} \to \text{Same Cylinder} \to \text{Adjacent Cylinder} \qquad (\text{Furthest})$$
Minimise access delay by placing files sequentially on the disk.
- Can use defragmentation software to reorganise files on disk to reduce access times (e.g same file, adjacent blocks on disk)
- Sequential access is much faster than random access ($10\times$)
## Optimisations
- Promote sequential access: Place related data together
- Avoid using disk if possible: cache in memory
- Align to disk page size, reduce the number of pages touched when loading.
- Use [[Shingled Magnetic Recording]]
