## Definition
Given some CPU intensive process $CPU_P$ and some IO bound processes, operating on a single hardware thread. On a non-preemptive FCFS system. *Note: $CPU_P$ does lots of compute, then a small bit of IO*
1. $CPU_P$ is forced to wait while the IO processes run for a short period of time, before being blocked. 
2. IO processes now wait for IO, $CPU_P$ can now run.
3. IO is completed, but the IO processes cannot run as the $CPU_P$ is still going
4. $CPU_P$ completes, and blocks on some small IO
5. IO processes can now run, but are forced to wait for IO as $CPU_P$ is using this (waiting)
As a result, the IO processes are forced to wait because of a CPU intensive process.