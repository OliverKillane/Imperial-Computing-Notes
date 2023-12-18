## Description
A system requiring a single deployment.
- Typically built with the same technology, as a single binary, running as a single process.
- Alternative to [[Microservice]]

| Type | Description |
|-|-|
| Single-Process Monolith | A single process, tightly coupled / classic monolith |
| Modular Monolith | The monolith is logically separated into modules (e.g being some service), with each module effectively being its owns service (e.g each on a thread) |
| Distributed Monolith | A modular monolith with each module having its own database |

Some very tightly coupled services may be multiple processes, but can act as a monolith if deployment of one requires upgrade and deployment of others. 
- On a spectrum with [[Monolith]] at the opposing end
## Communication
All communication can occur in memory, can be as cheap as an inlined function call.
- Need to ensure correct communication (e.g race conditions)
- Need to be careful about control flow (e.g get stuck in a tight loop)