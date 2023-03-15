---- MODULE BoundedFIFO ----
EXTENDS Naturals, Sequences
CONSTANT Messages, N
VARIABLES in, out, buffer
Vars == <<in, out, buffer>>

In == INSTANCE Channel WITH Data <- Messages, channel <- in
Out == INSTANCE Channel WITH Data <- Messages, channel <- out

\* In and out invariants hold, and the buffer is within the infinite set of sequences that only contain items in Messages
Type == In!Type /\ Out!Type /\ buffer \in Seq(Messages)

\* We ensure the size constant is correct
ASSUME (N \in Nat) /\ (N > 0)

------------------------------

\* Init requires init for in and out channels and an empty buffer
Init == In!Init /\ Out!Init /\ buffer = <<>>

\* Sending to in does not change buffer or out, uses In channel's receive
SendIn == LET Send(msg) == In!Send(msg) /\ UNCHANGED <<out, buffer>> IN \E msg \in Messages : Send(msg)
\* Receiving from in appends to the buffer, but does not changed the output (buffered)
ReceiveIn == In!Receive /\ buffer' = Append(buffer, in.value) /\ UNCHANGED out

\* Sending to out requires the buffer be non-empty, and takes from the head of the buffer. In is unchanged
SendOut == buffer # <<>> /\ Out!Send(Head(buffer)) /\ buffer' = Tail(buffer) /\ UNCHANGED in
\* Receiving from out does not changed buffer or in, but does require Out's receive
ReceiveOut == Out!Receive /\ UNCHANGED <<in, buffer >>

\* Can do one of four actions in each step
Next == (SendIn \/ ReceiveIn \/ SendOut \/ ReceiveOut) /\ (ReceiveIn => (Len(buffer) < N))

\* Next is a stuttering action
Spec == Init /\ [][Next]_Vars
------------------------------
Typed == []Type
==============================
