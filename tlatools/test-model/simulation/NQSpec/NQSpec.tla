------------------------------- MODULE NQSpec -------------------------------
EXTENDS Integers, Sequences

CONSTANTS EnQers, DeQers, Data, InitData, Ids, Busy, NoData

ASSUME InitData \in Data

Done == CHOOSE D : D \notin Data
\*Busy == CHOOSE D : D \notin Data
NotAnId == CHOOSE i : i \notin Ids
\*NoData == CHOOSE D : D \notin Data
Elements == [data : Data, id : Ids]
NotAnElement == CHOOSE E : E \notin Elements

VARIABLES enq, deq, after, adding
vars == <<enq, deq, after, adding>>

elts == DOMAIN after

doneElts == elts \ {adding[e] : e \in EnQers}

TypeOK == /\ enq \in [EnQers -> Data \cup {Done}]
          /\ deq \in [DeQers -> Data \cup {Busy}]
          /\ elts \in SUBSET Elements
          /\ after \in [elts -> SUBSET doneElts]
          /\ adding \in [EnQers -> Elements \cup {NotAnElement}]

Init == /\ enq = [e \in EnQers |-> Done]
        /\ deq = [d \in DeQers |-> InitData]
        /\ after = << >>
        /\ adding = [e \in EnQers |-> NotAnElement]
-----------------------------------------------------------------------------

Assign(var, idx, val) == var' = [var EXCEPT ![idx] = val]

IdsBeingAdded == {adding[el].id : el \in {e \in EnQers : adding[e] # NotAnElement}}

UnusedIds == (Ids \ {el.id : el \in elts}) \ IdsBeingAdded


AddElt(el) == 
  after' = [x \in elts \cup {el} |-> 
                 IF x = el THEN doneElts
                           ELSE after[x] ]
                           
RemoveElt(el) == 
  after' = [x \in elts \ {el} |-> after[x] \ {el}]

MinimalElts(After) == {el \in DOMAIN After : After[el] = {}}
minimalElts == MinimalElts(after)
      
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
             /\ UNCHANGED <<deq, after>>

\*  enq, deq, elts, after, adding
BeginDeq(d) == /\ deq[d] # Busy
               /\ Assign(deq, d, Busy)
               /\ UNCHANGED <<enq, after, adding>>
               
EndDeq(d) == /\ deq[d] = Busy
             /\ \E el \in minimalElts :
                  /\ RemoveElt(el)
                  /\ Assign(deq, d, el.data)
             /\ UNCHANGED <<enq, adding>>
             
Next == \/ \E e \in EnQers : BeginEnq(e)  \/ EndEnq(e)
        \/ \E d \in DeQers : BeginDeq(d)  \/ EndDeq(d)

Liveness == /\ \A e \in EnQers : WF_vars(BeginEnq(e)  \/ EndEnq(e))
            /\ \A d \in DeQers :  WF_vars(BeginDeq(d)  \/ EndDeq(d))
            
Spec == Init /\ [][Next]_vars  /\ Liveness

=============================================================================
\* Modification History
\* Last modified Sat Nov 14 16:00:53 PST 2015 by lamport
\* Created Thu Nov 05 15:07:25 PST 2015 by lamport
