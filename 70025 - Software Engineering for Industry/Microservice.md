## Definition
> Microservices are independently releasable services modelled around a business domain

Critically service is independent
- Independent deployment (location, time, etc)
- Independent tech (can use whatever tools/stack makes sense for the service)
- Independent failure (process failure only applies the the services)

## Communication Overhead
Need to use network to communicate through message passing
- Much higher cost than inter-thread (e.g shared memory) or function call communication
- Choices on protocol, data to be sent, possible failures, ordering of messages and connection state (see [[Stateless Services]]) 

## Reporting
- Complex communication means that failure investigation can be more complex (many components, many metrics, many logs)
