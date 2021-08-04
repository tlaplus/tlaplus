---------------------------- MODULE CMultiprocDefine ------------------------- 
EXTENDS Naturals, Sequences, TLC

(*   
--algorithm MultiprocDefine {
  variables n = 0 ;
  define { nplus1 == n + 1 
           nplus2 == nplus1 + 1 } ;
  process (Proc \in {1, 2, 3})
    variables i ;
    { main : i := nplus2 ;
             assert i = 2 ;
    } }
  
*)
                    
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-9c797e1d4e2fc4c259c478fdea1bd5fa
CONSTANT defaultInitValue
VARIABLES n, pc

(* define statement *)
nplus1 == n + 1
nplus2 == nplus1 + 1

VARIABLE i

vars == << n, pc, i >>

ProcSet == ({1, 2, 3})

Init == (* Global variables *)
        /\ n = 0
        (* Process Proc *)
        /\ i = [self \in {1, 2, 3} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "main"]

main(self) == /\ pc[self] = "main"
              /\ i' = [i EXCEPT ![self] = nplus2]
              /\ Assert(i'[self] = 2, 
                        "Failure of assertion at line 12, column 14.")
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ n' = n

Proc(self) == main(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2, 3}: Proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in {1, 2, 3} : WF_vars(Proc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-70c2856f6a2b2707884c9cedc014d866
=============================================================================
