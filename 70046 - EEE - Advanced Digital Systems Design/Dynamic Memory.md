## Definition
Uses a capacitor to store a charge to represent the bit held.
- Much smaller than a [[Static Memory#6T SRAM]]
- leakage from the capacitor requires periodic refresh
- Includes [[Synchronous Dynamic RAM]] and [[DDR SDRAM]]
Much like in [[RAM Organisation]] cells are organised by row and column.
## 1T DRAM
![[1T_Dynamic_Cell.png]]
## Access
| Pin | Name | Purpose |
| ---- | ---- | ---- |
| `A` | Address | contain address of cell |
| `D` | Data | Combined input/output (bidirectional).<br><br>Input when `WE_L` asserted (low) and `OE_L` disasserted (high).<br><br>Output when `WE_L` disasserted (High) and `OE_L` asserted (Low) |
| `RAS_L` | Row Address Low | Latch in row on low (edge-sensitive) |
| `CAS_L` | Column Address Low | Latch in column on low (edge-sensitive) |
| `WE_L` | Write Enable Low | enable writes (edge-sensitive) |
| `OE_L` | Output Enable Low | enable output (`D` is input also) (edge-sensitive) |
### Latency
| Property | Description | 4Mbit DRAM Performance with $t_{RAC} = 60 \ ns$ |
| ---- | ---- | ---- |
| $t_{RAC}$ | Minimum time from `RAS` fall to valid data output. (Set row, wait for output) | $60 \ ns$ |
| $t_{RC}$ | Minimum time from one row access to the next. | $110 \ ns$ |
| $t_{CAC}$ | Minimum time from `CAS` fall to valid data output. (Set column, wait for output) | $15 \ ns$ |
| $t_{PC}$ | Minimum time from one column access to the next. | $35 \ ns$ |
- Accessing different rows is more expensive than different columns. So more same-row access is better.
