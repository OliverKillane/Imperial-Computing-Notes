## [Paper Link](https://comp97109.doc.ic.ac.uk/reading/qmail.pdf)

## Description
The author discusses their techniques for improving security in a *mail transfer agent* forwarding application called *qmail*, in comparison to an existing application called *SendMail*.

One key message: *reduce the amount of bugs by reducing the amount of code*
- Reuse OS provided utilities (e.g. file system, pipes, etc)
- Simplify and profile later if performance becomes and issue (interpreters can be valuable for security, and worth the performance caveat)
- Remove trust from code - small amount of code that can be proven bug-free only.
- Remove hidden control flow.
- *Minimizing Privilege* reduces damage from security holes, but does not remove holes.

## Commentary
The *Minimizing Privilege* part seems strange, its listed as a distraction. 
- Then also used (albeit in a more strengthened form for the Jpeg transformation example)

Many of the bug related issues (handling failure, mutation, [[Generic Bugs]]) raised seems to be solvable also with better languages (i.e. functional, or even for systems Rust, or very strict safe subset of C++).
