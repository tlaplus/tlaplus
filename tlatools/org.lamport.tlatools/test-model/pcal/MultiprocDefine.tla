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
                    
\* BEGIN TRANSLATION (chksum(pcal) = "234d55b0" /\ chksum(tla) = "45423927")
CONSTANT defaultInitValue
VARIABLES pc, n

(* define statement *)
nplus1 == n + 1
nplus2 == nplus1 + 1

VARIABLE i

vars == << pc, n, i >>

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

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {1, 2, 3}: Proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
=============================================================================
