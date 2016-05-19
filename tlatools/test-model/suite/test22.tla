--------------- MODULE test22 -------------

(* Test of fingerprinting. *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x, y

S == {1}
T == {2, 3, 4}



Init ==  /\ Print("Distinct States should equal Distinct Initial States", TRUE)
         /\ x \in [S -> [S -> SUBSET T]]
         /\ y \in [S -> [S -> SUBSET [a : {2}, b : {3, 4, 5}]]]

Inv == IF [S -> [S -> SUBSET [b : {4, 4, 3, 5, 4}, a : {2, 2}]]] # 
               [S -> [S -> SUBSET [a : {2}, b : {3, 4, 5}]]]
          THEN Assert(FALSE, "Test 1 Failed")
          ELSE TRUE

Next ==     
  \/ UNCHANGED <<x, y>>

  \/ /\ x' \in [S -> [S -> SUBSET {4, 4, 4, 3, 2, 2}]]
     /\ UNCHANGED y

  \/ /\ y' \in [S -> [S -> SUBSET [b : {4, 4, 3, 5, 4}, a : {2, 2}]]]
     /\ UNCHANGED x

  \/ /\ y' = [y EXCEPT ![1][1] = {[b |-> 4, a |-> 2]}]
     /\ UNCHANGED x

  \/ /\ y' = [y EXCEPT ![1][1] = {[b |-> 3, a |-> 2]}]
     /\ UNCHANGED x

  \/ /\ y' = [y EXCEPT ![1][1] = {[b |-> 5, a |-> 2]}]
     /\ UNCHANGED x
=========================================
