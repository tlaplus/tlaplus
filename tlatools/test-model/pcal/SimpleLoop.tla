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
					
\* BEGIN TRANSLATION PC-846512b7e35fcd2f3db311b9b9ed86c1762665bd89ff7a245402dc1a1595c99c
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

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TPC-b7aa93405ee9c41f9956cf2c63b23ed91b3e157ff94da645336e295469627fc9
=============================================================================
