---- MODULE 24HourClock ----
EXTENDS Naturals, TLC
VARIABLE hour
-----------------------
Init == hour \in 0..23
Next == hour' = (hour + 1) % 24
        /\ (
            (hour <= 12 /\ PrintT(<<"[Morning] time:", hour>>)) 
         \/ (hour > 12 /\ hour < 18 /\ PrintT(<<"[Afternoon] time:", hour>>)) 
         \/ (hour >= 18 /\ PrintT(<<"[Evening] time:", hour>>))
        )
Spec == Init /\ <<Next>>_hour
-----------------------
Typed == []Init
====