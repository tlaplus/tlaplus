------------------------------ MODULE spanning ------------------------------
EXTENDS Integers
CONSTANTS Proc, NoPrnt, root, nbrs
ASSUME NoPrnt \notin Proc /\ nbrs \subseteq Proc \times Proc

VARIABLES prnt, rpt, msg
vars == <<prnt, rpt, msg>>

Init == /\ prnt = [i \in Proc |-> NoPrnt]
        /\ rpt = [i \in Proc |-> FALSE]
        /\ msg = {}

CanSend(i, j) ==  (<<i, j>> \in nbrs) /\ (i = root \/ prnt[i] # NoPrnt)

Update(i, j) == /\ prnt' = [prnt EXCEPT ![i] = j]
                /\ UNCHANGED <<rpt, msg>>

Send(i) == \E k \in Proc: /\ CanSend(i, k) /\ (<<i, k>> \notin msg)
                          /\ msg' = msg \cup {<<i, k>>}
                          /\ UNCHANGED <<prnt, rpt>>

Parent(i) == /\ prnt[i] # NoPrnt /\ ~rpt[i]
             /\ rpt' = [rpt EXCEPT ![i] = TRUE]
             /\ UNCHANGED <<msg, prnt>>

Next == \E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
                          THEN Update(i, j)
                          ELSE \/ Send(i) \/ Parent(i)
                               \/ UNCHANGED <<prnt, msg, rpt>>

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(\E i, j \in Proc: IF i # root /\ prnt[i] = NoPrnt /\ <<j, i>> \in msg
                                     THEN Update(i, j)
                                     ELSE \/ Send(i) \/ Parent(i)
                                          \/ UNCHANGED <<prnt, msg, rpt>>)

TypeOK == /\ \A i \in Proc : prnt[i] = NoPrnt \/ <<i, prnt[i]>> \in nbrs
          /\ rpt \in [Proc -> BOOLEAN]
          /\ msg \subseteq Proc \times Proc

Termination == <>(\A i \in Proc : i = root \/ (prnt[i] # NoPrnt /\ <<i, prnt[i]>> \in nbrs))

OneParent == [][\A i \in Proc : prnt[i] # NoPrnt => prnt[i] = prnt'[i]]_vars

SntMsg == \A i \in Proc: (i # root /\ prnt[i] = NoPrnt => \A j \in Proc: <<i ,j>> \notin msg)

=============================================================================
\* Modification History
\* Last modified Mon Jul 09 13:30:26 CEST 2018 by tthai