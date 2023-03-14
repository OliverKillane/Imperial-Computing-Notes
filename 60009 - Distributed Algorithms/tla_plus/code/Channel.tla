---- MODULE Channel ----
EXTENDS Naturals
CONSTANT Data
VARIABLE channel

\* Check whether channel is in the set (created by use of ..) of valid records
Type == channel \in [value: Data, ready: 0 .. 1, ack: 0 .. 1]

------------------------
Init == Type /\ channel.ack = channel.ready

\* Set value to d and flip ready
Send(d) == channel.ready = channel.ack /\ channel' = [channel EXCEPT !.value =d, !.ready = 1 - @]

\* Flip ack, otherwise leave channel the same
Receive == channel.ready # channel.ack /\ channel' = [channel EXCEPT !.ack = 1 - @]

\* Can only send valuesa that are in Data
SendSome == \E d \in Data : Send(d)

\* Either send or receieve (note can both send and recieve at the same time)
Next == SendSome \/ Receive

Spec == Init /\ [] [Next]_channel
------------------------
Typed == []Type
========================