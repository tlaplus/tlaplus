--------------------------- MODULE MCAlternatingBit -------------------------
EXTENDS AlternatingBit

INSTANCE ABCorrectness 

CONSTANTS msgQLen, ackQLen

SeqConstraint == /\ Len(msgQ) \leq msgQLen
                 /\ Len(ackQ) \leq ackQLen

SentLeadsToRcvd == \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)
=============================================================================

ImpliedAction == [ABCNext]_cvars

TNext == WF_msgQ(~ABTypeInv')
TProp == \A d \in Data : (sent = d) => [](sent = d)

CSpec == ABSpec /\ TNext

\* DataPerm == Permutations(Data)
==============================================================
