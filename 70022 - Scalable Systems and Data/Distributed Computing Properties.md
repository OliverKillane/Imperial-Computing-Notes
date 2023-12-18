### Scalability
- Aggregation of many different resources (cpu, memory, network)
- Software needs to distribute sub-tasks independent tasks for parallel compute to allow scaling with task size
### Fault Tolerance
- Need to mask failures from end-users
- Data and service redundancy via replication
### Load Balancing
- Needs high availability under load, SLAs often enforces (e.g need to compensate clients for failure to meet avg latency requirement)
- Need to provide predictable performance to clients
### Performance
- (like with DBMS) need to ensure data computed has consistent results 
- Can be limited by the slowest service (e.g waiting for last sub-task to be complete) (e.g one server is a *straggler*)