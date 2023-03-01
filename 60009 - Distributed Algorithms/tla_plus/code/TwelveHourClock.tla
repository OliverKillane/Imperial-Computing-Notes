---- MODULE TwelveHourClock ----
EXTENDS Naturals
VARIABLE hour
-----------------------
Init == hour \in 0..11
Next == hour' = (hour + 1) % 12 
Spec == Init /\ [][Next]_hour
-----------------------
Typed == []Init
====