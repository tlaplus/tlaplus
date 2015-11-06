------------------------------- MODULE NQSpec -------------------------------
EXTENDS Integers, Sequences

CONSTANTS EnQers, DeQers, Data, InitData, Ids

ASSUME InitData \in Data

Done == CHOOSE D : D \notin Data
Busy == CHOOSE D : D \notin Data
NotAnId == CHOOSE i : i \notin Ids
NotData == CHOOSE D : D \notin Data
Elements == [data : Data, id : Ids]
NotAnElement == CHOOSE E : E \notin Elements

VARIABLES enq, deq, elts, after, adding
vars == <<enq, deq, elts, after, adding>>



TypeOK == /\ enq \in [EnQers -> Data \cup {Done}]
          /\ deq \in [DeQers -> Data \cup {Busy}]
          /\ elts \in SUBSET Elements
          /\ after \in [elts -> SUBSET elts]
          /\ adding \in [EnQers -> Elements \cup {NotAnElement}]

Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq = [d \in DeQers |-> InitData]
        /\ elts = {}
        /\ after = << >>
        /\ adding = [e \in EnQers |-> NotAnElement]
-----------------------------------------------------------------------------

Assign(var, idx, val) == var' = [var EXCEPT ![idx] = val]

UnusedIds == Ids \ {el.id : el \in elts}

AddElt(el) == 
  /\ elts' = elts \cup {el}
  /\ after' = [x \in elts' |-> 
                 IF x = el THEN elts \ {adding[e] : e \in EnQers}
                           ELSE after[x] ]
                           
RemoveElt(el) == 
  /\ elts' = elts \ {el}
  /\ after' = [x \in elts' |-> after[x] \ {el}]

minimalElts == {el \in elts : after[el] = {}}
      
BeginEnq(e) == /\ enq[e] = Done 
               /\ \E D \in Data, id \in UnusedIds : 
                     LET el == [data |-> D, id |-> id]
                     IN  /\ Assign(enq, e, D)
                         /\ AddElt(el)
                         /\ Assign(adding, e, el)
               /\ UNCHANGED deq
                           
EndEnq(e) == /\ enq[e] # Done
             /\ Assign(enq, e, Done)
             /\ Assign(adding, e, NotAnElement)
             /\ UNCHANGED <<deq, elts, after>>

\*  enq, deq, elts, after, adding
BeginDeq(d) == /\ deq[d] # Busy
               /\ Assign(deq, d, Busy)
               /\ UNCHANGED <<enq, elts, after, adding>>
               
EndDeq(d) == /\ deq[d] = Busy
             /\ \E el \in minimalElts :
                  /\ RemoveElt(el)
                  /\ Assign(deq, d, el.data)
             /\ UNCHANGED <<enq, adding>>
             
Next == \/ \E e \in EnQers : BeginEnq(e)  \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d)  \/ EndDeq(d)

Liveness == /\ \A e \in EnQers : WF_vars(BeginEnq(e)  \/ EndEnq(e))
            /\ \A d \in DeQers :  WF_vars(BeginDeq(d)  \/ EndDeq(d))
            
Spec == Init /\ [][Next]_vars /\ Liveness

=============================================================================
\* Modification History
\* Last modified Thu Nov 05 16:16:15 PST 2015 by lamport
\* Created Thu Nov 05 15:07:25 PST 2015 by lamport
