## Definition
A large group of networked servers (typically commodity hardware with the exception of network)
- Designed for scale-out (more machines) rather than scale-out (better machines).
- Software is designed with the assumption of failure (small failures on large scale) and is often custom for the provider.
- Economies of scale work for management, hardware purchase, energy, operations.

*alternatively...*
A physical facility containing computing and storage infrastructure.
- Lots of networked machines, some with specialism (more storage, GPUs, better CPUs)
- Power, shelter, cooling and both software & physical security

Typically managed by [[Cloud Computing]] services.
### Commodity Machines
- Many low-cost / commodity machines rather than using HPC/specialised compute (e.g IBM mainframes)
- Rather than large machines with shared memory, smaller machines with no-shared memory, communicating by message passing
### Disaggregation
- Disaggregated data centres (one large machine with many different resources)
- The data centre as one machine, sharing resources, no-shared-memory 
## Reliability
- Build reliable systems out of unreliable components (fault tolerance)
the ANSI-TIA-942 Telecommunications Infrastructure Standard for Data Centres specifies a tiering system for datacentres:

| Tier | Generators | UPSs | Power Feeds | HVAC | Availability | Description |
|-|-|-|-|-|-|-|
| 1 | $0$ | $n$ | Single | $n$ | $99.671\%$ | Basic Site Infrastructure |
| 2 | $n$ | $n+1$ | Single | $n+1$ | $99.741\%$ | Redundant Capacity Component Site Infrastructure |
| 3 | $n+1$ | $n+1$ | Dual, switchable | N+1 | $99.982\%$ | Concurrently Maintainable Site Infrastructure |
| 4 | $2n$ | $2n$ | Dual, simultaneous | $2n$ | $99.995\%$ | Fault-Tolerant Site Infrastructure |

## Costs
### Capital Expenditure
Upfront investment to build the datacentre.
- Construction of the building, hardware purchase
- Energy grid connect, planning & planning permissions
### Operational Expenditure
Repeat operational costs:
- Energy (for machines and cooling costs)
- Maintenance (cleaning, replacing failed components)
- Physical security

$$\text{Power Usage Effectiveness (PUE)} = \cfrac{\text{Energy to Computing Equipment (servers, network, storage)}}{\text{Total Energy to Data Centre (cooling, UPS, switch gear, generators, PDUs, batteries, lights, fans)}}$$

For example [Google's PUE](https://www.google.com/about/datacenters/efficiency/) 
## Cost Reduction
### Increase Temperature of Aisles
Increasing temperature can increase rates of component failure, but lowers cooling requirement.
- Typically 18-20 degrees
- [[Google Cloud Platform]] at 27 degrees
### Reduce Inefficiency
- More power efficient hardware (e.g google uses higher voltage motherboards - lower current less heat)
- Cold vs Hot Aisle Containment
### Colder Environment
- Less cooling requirement
- Microsoft investigating underwater datacenters (lower sea temperature + easier cooling, cannot be maintained in the same way).
- Google's barges
### Improve Resource Utilisation
$$\text{Energy consumption} \not\propto \text{Compute Load}$$
- Idling hardware is expensive, making 100% use of compute is optimal.
- Virtualise and consolidate many services on a single server

One concept is hyperscale computing, treating the entire data centre as a single warehouse-scale computer with resources to virtualize.
- Entire data centre can be managed in software as a single system
- Can have specialised machines, with resources pooled (e.g some storage focussed, some for heavy CPU compute, etc)
- [[Software Defined Networking]]
## Extra
- [The Datacenter as a Computer: Designing Warehouse-Scale Machines, Third Edition | SpringerLink](https://link.springer.com/book/10.1007/978-3-031-01761-2)
- 
