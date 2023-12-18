When [[Microservice|microservices]] become inter-dependent

| Strength | Type | Description |
|-|-|-|
| 🔵 | Domain | Must interact to use functionality |
| 🟢 | Pass Through | Microservice gets and passes data to another microservice (may fetch data from anther microservice) |
| 🟠 | Common | Services use the same set of data (e.g share a database) |
| 🔴 | Content | External service changes internal service state (ownership/control over data not clear) |

- More coupling means more changes required per feature change. 
- More change requirements means more development time
- Better designs clearly separate external and internal interfaces
- Better designs clearly show and enforce single ownership over logically separate data

Large practical application is avoiding shared access to mutate a database.


