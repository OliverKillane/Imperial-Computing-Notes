---- MODULE AsyncMessage ----
EXTENDS Naturals
CONSTANT Data

VARIABLES value, ready, ack
Vars == << value, ready, ack >> \* Collection of variables values
Type == value \in Data /\ ready \in {0,1} /\ ack \in {0,1}
-----------------------------

\* Initial state
Init == value \in Data /\ ready \in {0,1} /\ ack = ready

\* Action to send a message (not yet acknowledged)
Send == ready = ack /\ value' \in Data /\ ready' = 1 - ready /\ UNCHANGED <<ack>>

\* Action to recieve a message with acknowledgement
Receive == ready # ack /\ ack' = 1 - ack /\ UNCHANGED <<value, ready>>

\* Module can either send or recieve (cannot do both due to unchanged in both actions)
Next == Send \/ Receive

\* Init is true, and next is always true with Vars potentially changed
Spec == Init /\ [][Next]_Vars
-----------------------------
\* Constraints: Value is always in data, ready & ack are always 0 or 1
Typed == []Type
============================