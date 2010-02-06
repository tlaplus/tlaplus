------------------- MODULE ABCorrectness --------------------
EXTENDS Naturals
CONSTANTS Data
VARIABLES sBit, sAck, rBit, sent, rcvd  
-------------------------------------------------------------
ABCInit == /\ sBit \in {0, 1}
           /\ sAck = sBit
           /\ rBit = sBit
           /\ sent \in Data
           /\ rcvd \in Data

CSndNewValue(d) == /\ sAck = sBit
                   /\ sent' = d
                   /\ sBit' = 1 - sBit
                   /\ UNCHANGED <<sAck, rBit, rcvd>>

CRcvMsg == /\ rBit # sBit 
           /\ rBit' = sBit
           /\ rcvd' = sent
           /\ UNCHANGED <<sBit, sAck, sent>>

CRcvAck == /\ rBit # sAck
           /\ sAck' = rBit
           /\ UNCHANGED <<sBit, rBit, sent, rcvd>>

ABCNext == \/  \E d \in Data : CSndNewValue(d) 
           \/  CRcvMsg \/ CRcvAck 
-------------------------------------------------------------
cvars == <<sBit, sAck, rBit, sent, rcvd>>

TypeInv == /\ sBit \in {0, 1}
           /\ sAck \in {0, 1}
           /\ rBit \in {0, 1}
           /\ sent \in Data
           /\ rcvd \in Data

ABCFairness == WF_cvars(CRcvMsg) /\ WF_cvars(CRcvAck)   

ABCSpec == ABCInit /\ [][ABCNext]_cvars /\ ABCFairness
==============================================================
