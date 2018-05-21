---------------------------- MODULE MultiprocDefine -------------------------- 
EXTENDS Naturals, Sequences, TLC

(*   
--algorithm MultiprocDefine
  variables n = 0 ;
  define nplus1 == n + 1 
         nplus2 == nplus1 + 1
  end define ;
  process Proc \in {1, 2, 3}
  variables i ;
  begin  main : i := nplus2 ;
                assert i = 2 ;
  end process
  end algorithm
*)
					
(***** BEGIN TRANSLATION ***)
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
                        "Failure of assertion at line 13, column 17.")
              /\ pc' = [pc EXCEPT ![self] = "Done"]
              /\ n' = n

Proc(self) == main(self)

Next == (\E self \in {1, 2, 3}: Proc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

(***** END TRANSLATION ***)
=============================================================================
