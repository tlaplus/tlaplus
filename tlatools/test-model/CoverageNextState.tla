-------------------------- MODULE CoverageNextState ------------------------
(**************************************************************************)
(*  Issue  92   https://github.com/tlaplus/tlaplus/issues/92              *)
(*                                                                        *)
(* TLC reports zero coverage for the conjunct of the next-state actions.  *)
(**************************************************************************)
EXTENDS Integers

VARIABLES y, state

-----------------------------------------------------------------------------

Init == (state = "eins") /\ (y = 0)


(***************************************************************************
    The more simplified example, plus a second NSA, from Issue 92.
 ***************************************************************************)
Jest == /\ state = "eins"  
        /\ y' \in 800..1000
        /\ y' \in 0..5000   \* Reports 0 coverage
        /\ state' = "deux"
        /\ state' = "deux"  \* Reports 0 coverage


(***************************************************************************
    ... and the more expanded example from Issue 92.
 ***************************************************************************)
A == \/ /\ state = "deux"
        /\ y' = 888
     \/ /\ state = "eins"
        /\ y' = y
        
APlus == /\ A
         /\ \/ /\ y' # y
               /\ state' = "three"
            \/ /\ y' = y   \* Reports 0 coverage
               /\ state' = "three"

Next == Jest \/ APlus

=============================================================================
\* Modification History
\* Last modified Mon Oct 23 08:03:01 PDT 2017 by loki
\* Created Tue Oct 17 17:14:16 PDT 2017 by loki