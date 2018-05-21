------------------------------ MODULE TestTabs ------------------------------ 
\* Warning: there are evil tabs in this file.
EXTENDS Naturals, TLC
(*
--algorithm TestTabs
  variables x = 0 ;
  begin
l:  x := IF /\ \A i \in {1} : 1 + 1 = 2
	    /\ \A i \in {1} : 2 + 2 = 4
  	    /\	\/ \A i \in {1} : 
		   1 = 0
		\/ \A i \in {1} : 1 = 2
 	        \/ \A i \in {1} : 1 = 1
          THEN 1
          ELSE 0 ;
    assert x = 1 ;
  end algorithm
*)
(* BEGIN TRANSLATION *)
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "l"

l == /\ pc = "l"
     /\ x' = (IF /\ \A i \in {1} : 1 + 1 = 2
                 /\ \A i \in {1} : 2 + 2 = 4
                 /\  \/ \A i \in {1} :
                        1 = 0
                     \/ \A i \in {1} : 1 = 2
                     \/ \A i \in {1} : 1 = 1
               THEN 1
               ELSE 0)
     /\ Assert(x' = 1, "Failure of assertion at line 16, column 5.")
     /\ pc' = "Done"

Next == l
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

(* END TRANSLATION *)
=============================================================================
