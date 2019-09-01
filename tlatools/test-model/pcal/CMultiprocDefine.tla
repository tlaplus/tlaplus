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
					
\* BEGIN TRANSLATION PC-5df847a77f754a7dc24602c8e9c42d08a36b0244365061f77f34e895d19a98dc
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

\* END TRANSLATION TPC-7d01b66d282f4cbad87c513b02e3dd43528dcf06a5fdbf02243c55908c63e85e
=============================================================================
