## Definition
A memory protection process for operating systems to guard against buffer overflow attacks by randomising the layout of executables loaded to memory.

In order to exploit a buffer overflow to manipulate some code/data, the location of the buffer relative to said target code needs to be known, randomisation breaks this.
