------------------------------- MODULE QSpec -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS EnQers, DeQers, Data, Done, Busy, NoData, InitData

ASSUME /\ Done     \notin Data
       /\ Busy     \notin Data
       /\ NoData   \notin Data
       /\ InitData \in Data

VARIABLES enq, deq, queue, enqInner, deqInner
vars == <<enq, deq, queue, enqInner, deqInner>>

TypeOK == /\ enq \in [EnQers -> Data \cup {Done}]
          /\ deq \in [DeQers -> Data \cup {Busy}]
          /\ queue \in Seq(Data)
          /\ enqInner \in [EnQers -> {Done, Busy}]
          /\ deqInner \in [DeQers -> {NoData} \cup Data]

Init == \* /\ PrintT("begin")
        /\ enq = [e \in EnQers |-> Done]
        /\ deq = [d \in DeQers |-> InitData]
        /\ queue = << >>
        /\ enqInner = [e \in EnQers |-> Done] \* /\ PrintT("foo")
        /\ deqInner = [d \in DeQers |-> InitData] \* /\ PrintT("bar")
        
BeginEnq(e) == /\ enq[e] = Done 
               /\ \E D \in Data : enq' = [enq EXCEPT ![e] = D]
               /\ enqInner' = [enqInner EXCEPT ![e] = Busy]
               /\ UNCHANGED <<deq, queue, deqInner>>
               
DoEnq(e) == /\ enqInner[e] = Busy
            /\ queue' = Append(queue, enq[e])
            /\ enqInner' = [enqInner EXCEPT ![e] = Done]
            /\ UNCHANGED <<deq, enq, deqInner>>
            
EndEnq(e) == /\ enq[e] # Done
             /\ enqInner[e] = Done
             /\ enq' = [enq EXCEPT ![e] = Done]
             /\ UNCHANGED <<deq, queue, enqInner, deqInner>>

BeginDeq(d) == /\ deq[d] # Busy
               /\ deq' = [deq EXCEPT ![d] = Busy]
               /\ deqInner' = [deqInner EXCEPT ![d] = NoData]
               /\ UNCHANGED <<enq, queue, enqInner>>
               
DoDeq(d) == /\ deq[d] = Busy
            /\ deqInner[d] = NoData
            /\ queue # << >>
            /\ deqInner' = [deqInner EXCEPT ![d] = Head(queue)]
            /\ queue' = Tail(queue)
            /\ UNCHANGED <<enq, deq, enqInner>>

EndDeq(d) == /\ deq[d] = Busy
             /\ deqInner[d] # NoData
             /\ deq' = [deq EXCEPT ![d] = deqInner[d]]
             /\ UNCHANGED <<enq, queue, enqInner, deqInner>>
             
Next == \/ \E e \in EnQers : BeginEnq(e) \/ DoEnq(e) \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d) \/ DoDeq(d) \/ EndDeq(d)
        
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Sat Nov 14 12:56:11 PST 2015 by lamport
\* Created Wed Nov 04 15:29:04 PST 2015 by lamport
