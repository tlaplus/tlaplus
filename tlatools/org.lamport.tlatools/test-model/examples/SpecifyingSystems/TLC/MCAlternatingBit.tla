--------------------------- MODULE MCAlternatingBit -------------------------
EXTENDS AlternatingBit, TLC, TLCExt

INSTANCE ABCorrectness 

CONSTANTS msgQLen, ackQLen

SeqConstraint == /\ Len(msgQ) \leq msgQLen
                 /\ Len(ackQ) \leq ackQLen

SentLeadsToRcvd == \A d \in Data : (sent = d) /\ (sBit # sAck) ~> (rcvd = d)

PermanentBitDisagreement == <>[](sBit # rBit)

CONSTANT d1, d2

PostCondition ==
   CounterExample = 
   [ action |->
      { << << 1,
              [ msgQ |-> <<>>,
                ackQ |-> <<>>,
                sent |-> d1,
                sBit |-> 0,
                sAck |-> 0,
                rcvd |-> d1,
                rBit |-> 0 ] >>,
           [ name |-> "SndAck",
             location |->
                 [ beginLine |-> 47,
                   beginColumn |-> 11,
                   endLine |-> 48,
                   endColumn |-> 61,
                   module |-> "AlternatingBit" ] ],
           << 2,
              [ msgQ |-> <<>>,
                ackQ |-> <<0>>,
                sent |-> d1,
                sBit |-> 0,
                sAck |-> 0,
                rcvd |-> d1,
                rBit |-> 0 ] >> >>,
        << << 2,
              [ msgQ |-> <<>>,
                ackQ |-> <<0>>,
                sent |-> d1,
                sBit |-> 0,
                sAck |-> 0,
                rcvd |-> d1,
                rBit |-> 0 ] >>,
           [ name |-> "RcvAck",
             location |->
                 [ beginLine |-> 50,
                   beginColumn |-> 11,
                   endLine |-> 53,
                   endColumn |-> 55,
                   module |-> "AlternatingBit" ] ],
           << 1,
              [ msgQ |-> <<>>,
                ackQ |-> <<>>,
                sent |-> d1,
                sBit |-> 0,
                sAck |-> 0,
                rcvd |-> d1,
                rBit |-> 0 ] >> >> },
  state |->
      { << 1,
           [ msgQ |-> <<>>,
             ackQ |-> <<>>,
             sent |-> d1,
             sBit |-> 0,
             sAck |-> 0,
             rcvd |-> d1,
             rBit |-> 0 ] >>,
        << 2,
           [ msgQ |-> <<>>,
             ackQ |-> <<0>>,
             sent |-> d1,
             sBit |-> 0,
             sAck |-> 0,
             rcvd |-> d1,
             rBit |-> 0 ] >> } ]
=============================================================================

ImpliedAction == [ABCNext]_cvars

TNext == WF_msgQ(~ABTypeInv')
TProp == \A d \in Data : (sent = d) => [](sent = d)

CSpec == ABSpec /\ TNext

\* DataPerm == Permutations(Data)
==============================================================
