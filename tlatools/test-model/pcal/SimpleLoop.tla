----------------------------- MODULE SimpleLoop ----------------------------- 
EXTENDS Naturals, TLC
(*

   --algorithm SimpleLoop                                                  
     variable x = 0;                                                     
     begin a : while x < 10                                              
                 do x := x+1 ;                                           
                    skip ;                                               
                    print x;                                             
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
                /\ PrintT(x')
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
