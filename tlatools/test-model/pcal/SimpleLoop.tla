----------------------------- MODULE SimpleLoop ----------------------------- 
EXTENDS Naturals, TLC
(*

   --algorithm SimpleLoop                                                  
     variable x = 0;                                                     
     begin a : while x < 10                                              
                 do x := x+1 ;                                           
                    skip ;                                               
                    assert x \in 1..10;                                             
               end while ;                                               
     end algorithm                                                         
*)
					
(******* BEGIN TRANSLATION *****)
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF x < 10
           THEN /\ x' = x+1
                /\ TRUE
                /\ Assert(x' \in 1..10, 
                          "Failure of assertion at line 10, column 21.")
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ x' = x

Next == a
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(******* END TRANSLATION *****)
=============================================================================
