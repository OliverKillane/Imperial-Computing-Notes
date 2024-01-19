## Definition
*From the paper: [Roofline: an insightful visual performance model for multicore architectures: Communications of the ACM: Vol 52, No 4](https://dl.acm.org/doi/10.1145/1498765.1498785)*

![[roofile_model.drawio.svg]]

For example the original paper compare floating point arithmetic performance, and memory bandwidth.
- We graph the attainable performance (i.e. $flops/s$ ) against the operational intensity (i.e. $flops/byte$). 
- The gradient is $bytes/s$ (the memory bandwidth)
- We get an increase up to a point (where $flops/s$ remains constant and it is compute bound)
