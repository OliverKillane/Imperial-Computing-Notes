---- MODULE LiveClock12 ----
EXTENDS Clock12

\* 
Fairness == WF_hour(Next)
LiveSpec == Spec /\ Fairness
----------------------------
\* There is always another hour
AlwaysTick == []<><<Next>>_hour

\* All hour states are always used in the future
AllTimes == \A hr \in 1 .. 12 : []<>(hour = hr)
==========================