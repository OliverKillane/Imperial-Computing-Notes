## Definition
A small multiported [[Static Memory]] array.
- We can implement read/write by using a multiplexor to select the input to the flipflop (either its output, or from the bit-line).
- A read line is used to open the output using a tristate-buffer.
![[Register_File_Cell.png]]
## Access
| Access | Description | Type |
| ---- | ---- | ---- |
| Read | Output is a combinational function of the address input. When address is changed, the output is immediately (at speed of silicon) changed (not reliant on clock). | Asynchronous |
| Write | Write can only occur when the flipflop allows, hence the write, select and data lines need to be on long enough to hit a clock-tick and update the flip flop's state. | Synchronous |
![[Register_file_read_write_timing.png]]
- Read changes continuously (combinational logic), but write only has effect of rising clock edge.
