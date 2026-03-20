-------------------------------- MODULE LockHS --------------------------------

(*****************************************************************************)
(* This module contains the specification of a lock with auxiliary variables.*)
(* 1. A history variable `h_turn` is needed to remember the assignement of   *)
(*    the turn variable used inside the Peterson specification.              *)
(* 2. A stuttering variable `s` is added to force the stuttering of the Lock *)
(*    specification to mimick the 3 steps taken by Peterson to enter the     *)
(*    critical section.                                                      *)
(* With these variables, one can finally refine LockHS to Peterson, giving   *)
(* an equivalence between the Lock and Peterson specifications.              *)
(*                                                                           *)
(* The stuttering is achieved using the Stuttering module created by Leslie  *)
(* Lamport and comes from to the paper "Auxiliary Variables in TLA+".        *)
(* The module used here has been modified, see explanations at the end of    *) 
(* the Stuttering module.                                                    *)
(*****************************************************************************)

EXTENDS Lock

\* History variable to remember the turn variable
VARIABLE h_turn
NoHistoryChange(A) == A /\ UNCHANGED h_turn

\* Stuttering variable
VARIABLE s
INSTANCE Stuttering

-------------------------------------------------------------------------------

Other(p) == IF p = 1 THEN 2 ELSE 1 

InitHS == Init /\ (h_turn = 1) /\ (s = top)

\* Adding 2 stuttering steps after an l1(self) transition
\* Updating the history variable during the right stutter step
l1HS(self) == 
  /\ PostStutter(l1(self), "l1", self, 1, 2, LAMBDA j : j-1)
  /\ h_turn' = IF s' # top THEN IF s'.val = 1 THEN Other(self)
                                              ELSE h_turn
                           ELSE h_turn

procHS(self) == 
  \/ NoStutter(NoHistoryChange(l0(self)))
  \/ l1HS(self)
  \/ NoStutter(NoHistoryChange(cs(self)))
  \/ NoStutter(NoHistoryChange(l2(self)))

NextHS == (\E self \in 1..2: procHS(self))

SpecHS == InitHS /\ [][NextHS]_<<vars, h_turn, s>>

-------------------------------------------------------------------------------

TypeOKHS == 
  /\ TypeOK
  /\ h_turn \in 1..2
  /\ s \in {top} \cup [id : {"l1"}, ctxt : {1, 2}, val : 1..2]

InvHS == 
  /\ \A p \in ProcSet : 
    /\ IF s # top THEN s.ctxt = p ELSE FALSE
    => pc[p] = "cs"
  /\ \A p \in ProcSet :
    \/ pc[p] = "l2"
    \/ pc[p] = "cs" /\ s = top
    \/ IF s # top THEN s.ctxt = p /\ s.val = 1 ELSE FALSE
    => h_turn = Other(p)

pc_translation(self, label, stutter) == 
  CASE (label = "l0") -> "a0"
    [] (label = "l1") -> "a1"
    [] (label = "l2") -> "a4"
    [] (label = "cs") -> IF stutter = top THEN "cs"
                         ELSE IF stutter.ctxt # self THEN "cs"
                         ELSE IF stutter.val = 2 THEN "a2"
                         ELSE IF stutter.val = 1 THEN "a3"
                         ELSE "error"
c_translation(alt_label) == 
  alt_label \in {"a2", "a3", "cs", "a4"}

P == INSTANCE Peterson WITH
      pc <- [p \in ProcSet |-> pc_translation(p, pc[p], s)],
      c <- [p \in ProcSet |-> c_translation(pc_translation(p, pc[p], s))],
      turn <- h_turn
PSpec == P!Spec

===============================================================================