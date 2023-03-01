---- MODULE OneBitClock ----
VARIABLE b
Type == b \in {0,1}
-----------------------------
Init == b=0 \/ b=1
Next == ((b=0) /\ (b'=1)) \/ ((b=1) /\ (b'=0))
Spec == Init /\ [][Next]_b
-----------------------------
Typed == []Type
====