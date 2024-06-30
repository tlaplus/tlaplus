--------------------------- MODULE NotSoSimpleLoop -------------------------- 
EXTENDS Naturals, TLC

(*   --algorithm NotSoSimpleLoop                                             
     variable x = 0;                                                     
     begin a : while x < 10                                              
                 do x := x+1 ;                                           
                    skip ;                                               
                    assert x \in 1..10
               end while ;                                               
               x := 4*x ;                                                
               assert x = 40 ;                                                 
           b : assert 2 * x = 80;                                             
     end algorithm                  *)

                    
\* BEGIN TRANSLATION (chksum(pcal) = "3acbf16a" /\ chksum(tla) = "f1d2d847")
VARIABLES pc, x

vars == << pc, x >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF x < 10
           THEN /\ x' = x+1
                /\ TRUE
                /\ Assert(x' \in 1..10, 
                          "Failure of assertion at line 9, column 21.")
                /\ pc' = "a"
           ELSE /\ x' = 4*x
                /\ Assert(x' = 40, 
                          "Failure of assertion at line 12, column 16.")
                /\ pc' = "b"

b == /\ pc = "b"
     /\ Assert(2 * x = 80, "Failure of assertion at line 13, column 16.")
     /\ pc' = "Done"
     /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
