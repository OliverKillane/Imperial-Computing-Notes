## Rack Definition
$$ \text{Single Server} \to \text{Rack} \to Cluster $$
A pre-packaged compute between a server & cluster.
- Contains ~42 *rack units/RU* that host computing resources.
- Contains CPU, accelerators, storage (cold/warm/hot disks + SSDs) and a networking interconnect (see [[Software Defined Networking]])

The future is full *resource disaggregation*, the system no longer provisions applications servers with resources, but rather has pooled all the resources in the rack (or even datacentre) for applications to use as if running on a single machine. 

Rack scale applications can use [[Remote Direct Memory Access]]