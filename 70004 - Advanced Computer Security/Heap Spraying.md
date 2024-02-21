## Definition
A technique used to make arbitrary code execution easier. 
1. The *heap spray* performs massive heap allocations
2. These enable exploits which rely on the trusted code being attacked reading values from the heap placed by the attacker.
3. Heap related memory safety issues in trusted code result in reading maliciously placed data
4. This data is typically code to be executed and is commonly used with a [[NOP Sled]].
