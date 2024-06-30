--------------------------- MODULE ReallySimpleMultiProc -------------------------- 
EXTENDS Naturals, TLC

(*   
--algorithm SimpleMultiProc                                             
     variables                                                           
       x = [i \in ProcSet |-> CASE i = 41 -> 1 []                         
                                  i = 42 -> 2 []                         
                                  i = 43 -> 3];                          
       sum = 0 ;                                                         
       done = {};                                                        
     process ProcA = 41                                                  
       variable y = 0;                                                   
       begin a1 : sum := sum + y + x [ 41 ] ||                           
                  done := done \cup { 41 } ;                             
             a2 : when done = { 41, 42, 43 } ;                           
                  when Print ( sum , TRUE ) ;                            
       end process                                                       
     process ProcB \in {42, 43}                                          
       variable z \in {2, 3} ;                                           
       begin b1 : sum := sum + z + x [ self ] ;                          
             b2 : done := done \cup { self } ;                           
       end process                                                       
     end algorithm         

*)
                    
\* BEGIN TRANSLATION (chksum(pcal) = "2bdc51cc" /\ chksum(tla) = "bf9f6e5d")
VARIABLES pc, x, sum, done, y, z

vars == << pc, x, sum, done, y, z >>

ProcSet == {41} \cup ({42, 43})

Init == (* Global variables *)
        /\ x = [i \in ProcSet |-> CASE i = 41 -> 1 []
                                      i = 42 -> 2 []
                                      i = 43 -> 3]
        /\ sum = 0
        /\ done = {}
        (* Process ProcA *)
        /\ y = 0
        (* Process ProcB *)
        /\ z \in [{42, 43} -> {2, 3}]
        /\ pc = [self \in ProcSet |-> CASE self = 41 -> "a1"
                                        [] self \in {42, 43} -> "b1"]

a1 == /\ pc[41] = "a1"
      /\ /\ done' = (done \cup { 41 })
         /\ sum' = sum + y + x [ 41 ]
      /\ pc' = [pc EXCEPT ![41] = "a2"]
      /\ UNCHANGED << x, y, z >>

a2 == /\ pc[41] = "a2"
      /\ done = { 41, 42, 43 }
      /\ Print ( sum , TRUE )
      /\ pc' = [pc EXCEPT ![41] = "Done"]
      /\ UNCHANGED << x, sum, done, y, z >>

ProcA == a1 \/ a2

b1(self) == /\ pc[self] = "b1"
            /\ sum' = sum + z[self] + x [ self ]
            /\ pc' = [pc EXCEPT ![self] = "b2"]
            /\ UNCHANGED << x, done, y, z >>

b2(self) == /\ pc[self] = "b2"
            /\ done' = (done \cup { self })
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << x, sum, y, z >>

ProcB(self) == b1(self) \/ b2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA
           \/ (\E self \in {42, 43}: ProcB(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcA)
        /\ \A self \in {42, 43} : WF_vars(ProcB(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
