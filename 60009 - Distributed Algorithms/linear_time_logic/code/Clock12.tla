---- MODULE Clock12 ----
EXTENDS Naturals
VARIABLE hour

\* 12 hour clock state constraint
Type == hour \in 1..12
-----------------------
\* Initial and Next Action
Init == Type
Next == hour' = (hour % 12) + 1

\* 
Spec == Init /\ [][Next]_hour
-----------------------

Typed == []Type
=======================