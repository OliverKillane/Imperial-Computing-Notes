## Definition
Rather than using the CPU to transfer data from main memory to a peripheral (wastes cycles), a separate DMA module does this (needs to update cache also).

*Note: Here we reference main memory but this could apply to any bus connected perhipheral or cache.*
## Modes
| Mode | Description | Speed |
| ---- | ---- | ---- |
| Burst | DMA gains access to system bus and releases it on task completion | Fastest |
| Cycle Stealing | DMA forces CPU to release bus, makes small transfer. Repeats until task is complete. | Slow |
| Transparent/Interleaving | DMA only takes control of the bus when the CPU does not need it. | Slowest |
