## Definition
A [[Dynamic Memory]] where the external interface is coordinated by an external clock.
- Previously changed in control signals had immediate affects (only delayed by distance for current to travel)
- Synchronous means each (clock - e.g. rising edge) the control input are applied.
- Allows for pipelining of access operations (each tick a new access can be made, accesses are overlapped for higher throughput)