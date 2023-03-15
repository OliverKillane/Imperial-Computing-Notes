---- MODULE AltBit ----
EXTENDS Naturals, Sequences
CONSTANTS Data
VARIABLES msgQ, ackQ, sBit, sAck, rBit, sent, recived

Vars == <<msgQ, ackQ, sBit, sAck, rBit, sent, recived>>

Unimplemented == TRUE
Type == Unimplemented
----------------------
Init == msgQ = <<>> /\ rBit = sBit  /\ send    \in Data /\ sBit \in {0,1} /\
        ackQ = <<>> /\ sAck = sBit  /\ recived \in Data /\ rBit = sBit

\* Insert message d to the msgQ
SendMsg(d) == sBit = sAck /\ sBit' = 1 - sBit /\ sent' = d /\ msgQ' = Append(msgQ, d) /\ UNCHANGED sAck

\* Resend the last message sent to msgQ
ResendMsg == sBit # sAck /\ msgQ' = Append(msgQ, sent) /\ UNCHANGED <<sBit, sAck, sent>>

\* Receive a message from the msgQ
ReceiveMsg == len(msgQ) > 0 /\ rBit' = 1 - rBit  /\ recived' = Head(msgQ)

\* SendAck (Send acknowledgment to AckQ)
SendAck == 

ReceiveAck == Unimplemented \* Receive acknowledgement


LoseMsg    == Unimplemented \* Lose a message from MsgQ (for testing)
LoseAck    == Unimplemented \* Lose an acknowledgement from MsgQ (for testing)

Next == \E d \in Data : SendMsg(d) 
     \/ ResendMsg  \/ ReceiveMsg \/ SendAck 
     \/ ReceiveAck \/ LoseMsg    \/ LoseAck
--------------------
\* Weak Fairness for ResendMsg & SendAck as eventually all messages are sent
\* just need to be resent and acknowledged.
\* Strong Fairness for ResendMsg & ReceiveAck as these are intermittently 
\* executed infinitely (continue to recieve forever)
Fair == WF_Vars(ResendMsg) /\ SF_Vars(ReceiveMsg)
     /\ WF_Vars(SendAck)   /\ SF_Vars(ReceiveAck)

Spec == Init /\ [][Next]_Vars /\ Fair
--------------------
Typed == []Type
====================