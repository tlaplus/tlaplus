------------------------------- MODULE Peterson -------------------------------

(*****************************************************************************)
(* This module contains the specification for Peterson's Algorithm, taken    *)
(* from the "Parallel Programming" course taught at ULiège.                  *)
(* The invariant `Inv` is the one presented in the course augmented by a     *)
(* clause representing mutual exclusion of the critical section              *)
(* A proof is given to show that `Inv` is inductive.                         *)
(* Moreover the refinement from Peterson to the abstract lock is also proven.*)
(*****************************************************************************)

EXTENDS Integers

Other(p) == IF p = 1 THEN 2 ELSE 1 

(*
--algorithm Peterson{
    variables
      c = [self \in ProcSet |-> FALSE],
      turn = 1;

    process(proc \in 1..2){
a0:   while(TRUE){
        skip;
a1:     c[self] := TRUE;
a2:     turn := Other(self);
a3:     await ~c[Other(self)] \/ turn = self;
cs:     skip;
a4:     c[self] := FALSE;
      }
    }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "1d547bc3" /\ chksum(tla) = "8de86c82")
VARIABLES pc, c, turn

vars == << pc, c, turn >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ c = [self \in ProcSet |-> FALSE]
        /\ turn = 1
        /\ pc = [self \in ProcSet |-> "a0"]

a0(self) == /\ pc[self] = "a0"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ UNCHANGED << c, turn >>

a1(self) == /\ pc[self] = "a1"
            /\ c' = [c EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ turn' = turn

a2(self) == /\ pc[self] = "a2"
            /\ turn' = Other(self)
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ c' = c

a3(self) == /\ pc[self] = "a3"
            /\ ~c[Other(self)] \/ turn = self
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << c, turn >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ UNCHANGED << c, turn >>

a4(self) == /\ pc[self] = "a4"
            /\ c' = [c EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a0"]
            /\ turn' = turn

proc(self) == a0(self) \/ a1(self) \/ a2(self) \/ a3(self) \/ cs(self)
                 \/ a4(self)

Next == (\E self \in 1..2: proc(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION 

TypeOK ==
  /\ c \in [ProcSet -> BOOLEAN]
  /\ turn \in ProcSet
  /\ pc \in [ProcSet -> {"a0", "a1", "a2", "a3", "cs", "a4"}]

lockcs(i) ==
  pc[i] \in {"cs", "a4"}
Inv ==
  /\ \A p \in ProcSet : c[p] <=> pc[p] \in {"a2", "a3", "cs", "a4"}
  /\ \A p \in ProcSet : pc[p] \in {"cs", "a4"} 
      => (turn = p \/ pc[Other(p)] \in {"a0", "a1", "a2"})
  /\ \A i, j \in ProcSet: (i # j) => ~(lockcs(i) /\ lockcs(j))

pc_translation(label) ==
  CASE (label = "a0") -> "l0"
    [] (label \in {"a1", "a2", "a3"}) -> "l1"
    [] (label \in {"cs"}) -> "cs"
    [] (label \in {"a4"}) -> "l2"

lock_translation == IF \E p \in ProcSet : pc[p] \in {"cs", "a4"} THEN 0 ELSE 1

L == INSTANCE Lock
     WITH pc <- [p \in ProcSet |-> pc_translation(pc[p])], 
     lock <- lock_translation
LSpec == L!Spec

-------------------------------------------------------------------------------

===============================================================================
