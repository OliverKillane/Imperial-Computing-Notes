## Layers
![[abstraction_layers.png]]
*Image is from ADSD slides*

| Level | Description | Objective |
| ---- | ---- | ---- |
| System |  | Defines partitions and the interfaces used to connect between them (e.g. communications, inter-processor, memory hierarchy) |
| Algorithm |  | Model the behaviour of the system. Simulations to ensure system implements an algorithm correctly. |
| [[Register Transfer Level\|RTL]]/[[Hardware Description Languages\|HDL]] | The functional level. (using SystemVerilog, VHDL, etc) | Defines the [[Microarchitecture]] , control and data paths, timing/clocking. |
| Gate | Connecting logic gates. | Define the behaviour of components/building blocks used in the [[Register Transfer Level\|RTL]] |
| Circuit |  | Implementing logic gate behaviour with transitors. |
| Device |  | Optimisation of [[Transistor]] parameters |
## Design Process
Top down and bottom up design strategies (refining & decomposing down to primitive components, versus building up from primitives).
- Usually a mixed strategy of mostly top-down with some bottom-up is used.
## Synthesis
$$\text{Specification} \to \text{System-Level Model} \to \text{algorithm} \to \text{RTL Model} \to \text{RTL Optimisation} \to \text{generic gate-level model} \to \text{Mapped gate-level model} \to \text{Place and Route}$$
- Mapped Gate-Level Model depends on the underlying technology (e.g. [[FPGA]] vs [[ASIC]])
