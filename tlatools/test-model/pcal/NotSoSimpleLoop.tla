--------------------------- MODULE NotSoSimpleLoop -------------------------- 
EXTENDS Naturals, TLC

(*   --algorithm NotSoSimpleLoop                                             
     variable x = 0;                                                     
     begin a : while x < 10                                              
                 do x := x+1 ;                                           
                    skip ;                                               
                    print x;                                             
               end while ;                                               
               x := 4*x ;                                                
               print x ;                                                 
           b : print 2 * x ;                                             
     end algorithm                  *)

					
(****** BEGIN TRANSLATION ****)
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
           ELSE /\ x' = 4*x
                /\ PrintT(x')
                /\ pc' = "b"

b == /\ pc = "b"
     /\ PrintT(2 * x)
     /\ pc' = "Done"
     /\ x' = x

Next == a \/ b
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

(****** END TRANSLATION ****)
=============================================================================
