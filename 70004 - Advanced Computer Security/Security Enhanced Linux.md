## Summary
Introduced by the NSA for securing linux assets.
- Enforces an admin-defined security policy ([[Mandatory Access Control]]) over all processes, objects and operations.
- Can confine services and applications (even running as root) to mitigate the risks of flawed or malicious programs

All subjects (processes) and objects (files, ports and other resources) are associated with labels used to describe authorisation.

When an operation occurs (e.g. opening a file), the request is redirected to a *policy engine* which determines if the subject can perform the operation.
- Deny all by default

![[SELinux_flow.svg]]
### Advantages
- Can confine the operations of privileged system daemons (reduces the impact of a daemon being misused by a malicious process)
- Centralized policy configuration is easier to manage and analyse than [[Discretionary Access Control]]'s scattered configuration.
### Limitations
- If the vulnerability used is in the kernel.
- If a security policy is permissive ([[Security Enhanced Linux]] will merely enforce the policy it is given)
## Type Enforcement
```python
# For each subject and object
f"{user}:{role}:{type}:{security level}"

# for example
facebook      = f"u:r:facebook:s0:c0" # level: s0 is sensitivity, c0 is category
sys_directory = f"u:r:sysfs:s0:c0" 

```
*Note: Android uses the type field to isolate processes, and level to isolate device users*
- Process types are called *domains*
- *Domains*/*types* are [[Security Equivalence Classes]]
- Same *domain*/*type* means same access & the subject/object is identified using this.
- The security level (sensitivity and zero of more categories) os determined by [[Multi-Level Security]]
![[domains_and_types.svg]]
### Rules
```python
f"allow {domain} {type}:{class} \{{permissions}\}"
"allow D1 T2:file read_write_execute"

f"neverallow {domain} {type}:{class} \{{permissions}\}"

# Disallow any system service apart from the dumpstate, shell etc of the domain attribute from executing files
"neverallow {domain -appdomain -dumpstate -shell -system_server -zygote} {file_type -system_file -exec_type}:file execute" 
```
*Note: [AVCRules - SELinux Wiki (selinuxproject.org)](https://selinuxproject.org/page/AVCRules)* 
- `neverallow` is used to ensure no `allow` rules are added in future that accidentally conflict (the `checkpolicy` compiler issues a warning).
- The last rule in a conflict is chosen
## Configuration

| Path                  | Description                                                                                                                        |
| --------------------- | ---------------------------------------------------------------------------------------------------------------------------------- |
| `*.te`                | Type Enforcement files (`D1.te`, `D2.te`, etc.) containing rules for a domain.                                                     |
| `file_contexts`       | File security contexts (labels for `\sys` at build time, `\dev, \data` at runtime).                                                |
| `mac_permissions.xml` | Assigns a seinfo tag to applications based on their signature (and optionally package name). Configuration is read during startup. |
| `seapp_contexts`      | Maps app UID (and optionally seinfo) to domain.                                                                                    |
## Android
Ported to android in 2012, and adopted in *permissive mode* in `4.3`, *enforcing mode* in `4.4`.

