\* PlusCal C-Syntax manual, Version 1.8, Appendix A, "The Grammar", page 57.
\* --fair and algorithm are two terminals, so a newline may separate them:
\*
\*     ⟨Algorithm⟩ ::= [ --algorithm | --fair algorithm ] ⟨name⟩
\*                     { ⟨VarDecls⟩0,1
\*                        ⟨Definitions⟩0,1
\*                        ⟨Macro⟩∗
\*                        ⟨Procedure⟩∗
\*                        [ ⟨CompoundStmt⟩ | ⟨Process⟩+ ] }
\*
\* This note stays outside the module. Inside the module, algorithm occurs
\* only at column zero, on the line after --fair.
------------------------------ MODULE SplitFairHeader ------------------------------
(*
--fair
algorithm A {
  { a: skip; }
}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "e52f8f73")
VARIABLE pc

vars == << pc >>

Init == /\ pc = "a"

a == /\ pc = "a"
     /\ TRUE
     /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION 
=============================================================================
