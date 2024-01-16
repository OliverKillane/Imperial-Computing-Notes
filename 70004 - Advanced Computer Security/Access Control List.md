## Definition
A list of permissions associated with a resource.


```python
[
	(Alice, "/home/Alice/*", {Read, Write, Execute}),
	(Alice, "/var/*", {Read, Write}),
	(Bob, "/home/Bob/*", {Read, Write}),
]
```
- Used in operating systems to associate permissions with files, (unix represents many resources as special files to use the same system)
- Can assign based on roles (e.g. Admin)

Can be modelled as:

| Model | Description |
| ---- | ---- |
| Mandatory | System decides exactly which users have permissions for resources |
| Discretionary | (Unix) Users authorised to determine who else can access files they have permissions for.  |
| Role Based | (Non-Discretionary) Role determines permissions. |
