--------------------------------- MODULE Lock ---------------------------------

(*****************************************************************************)
(* This module contains the specification of an abstract lock.               *)
(* The proof for mutual exclusion is also detailed.                          *)
(*****************************************************************************)

EXTENDS Integers

(*
--algorithm Lock{
    variables lock = 1;
    
    macro Lock(l){
      await l = 1;
      l := 0;
    }
    
    macro Unlock(l){
      l := 1;
    }
  
    process(proc \in 1..2){
l0:   while(TRUE){
        skip; \* non-critical section
l1:     Lock(lock);
cs:     skip; \* critical section
l2:     Unlock(lock);
      }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f820ffbb" /\ chksum(tla) = "24b4f3dd")
VARIABLES pc, lock

vars == << pc, lock >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ lock = 1
        /\ pc = [self \in ProcSet |-> "l0"]

l0(self) == /\ pc[self] = "l0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l1"]
            /\ lock' = lock

l1(self) == /\ pc[self] = "l1"
            /\ lock = 1
            /\ lock' = 0
            /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "l2"]
            /\ lock' = lock

l2(self) == /\ pc[self] = "l2"
            /\ lock' = 1
            /\ pc' = [pc EXCEPT ![self] = "l0"]

proc(self) == l0(self) \/ l1(self) \/ cs(self) \/ l2(self)

Next == (\E self \in 1..2: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK ==
  /\ lock \in {0, 1}
  /\ pc \in [ProcSet -> {"l0", "l1", "cs", "l2"}]

lockcs(i) ==
  pc[i] \in {"cs", "l2"}

LockInv == 
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))
  /\ (\E p \in ProcSet: lockcs(p)) => lock = 0

-------------------------------------------------------------------------------

WaitingLeadsToCS == (pc[1] = "l1") ~> (pc[1] = "cs")

===============================================================================
