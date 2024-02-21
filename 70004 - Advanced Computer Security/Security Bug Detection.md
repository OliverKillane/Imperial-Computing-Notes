## Runtime Monitoring
By [[Dynamic Analysis]] on instrumented software.
- Can be slow (instrumented binaries are necessarily slower), and often requires source access.
## Black-Box Testing
[[Black-Box Fuzzing]] and [[Fuzzing]] in general can be used to find bugs (e.g. [[CVE-2007-3944]]).
- Black box means no visibility of program logic, which can result in low coverage, and unknowable edge cases being missed.
- Can be done without access to code, or even done entirely externally (can fuzz other organisation's services & products) 
## Static Analysis
[[Static Analysis]] 