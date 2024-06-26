## Language Design
*Note: More information available from [Overview of Java SE Security (oracle.com)](https://docs.oracle.com/javase/8/docs/technotes/guides/security/overview/jsoverview.html)*
$$\text{Java} \underset{compile}{\longrightarrow} Bytecode \underset{interpret}{\longrightarrow} Execute$$
Java is compiled to a portable bytecode that is then interpreted.
- Bytecode comes in `.class` files
- Bytecode can be created manually, and is not necessarily produced by a java compiler.
The Java Virtual Machine loads the `.class`, and can then execute.
$$\text{Loader} \to \text{Verifier} \to \text{Linker} \to \text{Bytecode Interpreter}$$
Each program can have multiple threads with their own stacks, sharing a heap.
### Class Loader
A loader (potentially extending the default [ClassLoader](https://docs.oracle.com/javase/8/docs/api/java/lang/ClassLoader.html)) loads files (or from network) and extracts bytecode.
- This loading mechanism can be overridden and replaced
- The classloader used to load a given class is included in the class object
- Each class has a *protection domain* associated
 - [[Code Signing]] can be used in some circumstances to verify the origin of a class.  
### Verifier
Checks the bytecode prior to loading (security & correctness), throwing a `verifyError` on failure.

Given that there is no way to determine the source of some bytecode (i.e. if it was generated by `javac`, or manually constructed), bytecode cannot be trusted to be correct or not contain malicious non-java standard compliant code.
#### Correctness Checks
- Every instruction has a valid opcode, and obeys type discipline
- Every branch goes to the start of a valid instruction
- Access modifiers are not breached (e.g. access from outside class method to private member), including final (e.g. cannot extend `final class`)
- No operand stack overflows or underflows
- Methods have structurally correct signatures
A larger list of checks is available from 
### Linker
Adds a compiled class or interface to the runtime, initialises static fields, and resolves names to reference the correct loaded classes/methods/statics.
### Runtime Security
Checks for [[Generic Bugs]] are performed (for example array bounds checks, null pointer access checks). Furthermore pointer arithmetic is not supported, and garbage collection is automatic.
### Native Interaction
Bytecode can be compiled into native (e.g. x86, ARM) instructions, as well as interoped with native code compiled from C/C++/other languages.
- JIT is good for performance, and a core feature of [[HotSpot]]
- Required for interaction with OS, drivers, etc that present a system call interface, or library interface over the C ABI.
- Similarly C# and the [[Common Language Runtime]]

## Security Manager
Java library methods call the security manager to check permissions on operations.

When called at runtime the *Security Manager* assesses:
- The protection domain of the calling class (including the signer if [[Code Signing]] -  validated at load time, and the location of the java class)
- A system policy is used to allow or deny permission to call the java library method.

The checks usable can be found in the [SecurityManager documentation](https://docs.oracle.com/javase/8/docs/api/java/lang/SecurityManager.html#method.detail).

Stack inspection is used to determine the calling method.
- Permissions depend of the permission of methods above it on the stack.
- Vulnerabilities have been found in the implementation of this method (see [[10 Years of Java Exploits]])
 
