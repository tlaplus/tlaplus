If both the PlusCal algorithm and its translation have been changed since the
last time the translation was run (as detected by the hash code) then raise
a warning.
---- MODULE W4803_Test ----
(*
--algorithm Test {
  {
    lbl: skip;
  }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "00000000" /\ chksum(tla) = "00000000")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "lbl"

lbl == /\ pc = "lbl"
       /\ TRUE
       /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lbl
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====

