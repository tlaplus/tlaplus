------------------------------ MODULE FairSeq2 ------------------------------
EXTENDS Integers
(***************************************************************************
PlusCal options (version 1.5)
--fair algorithm FairSeq {
    variable x = 0 ;
    fair { while (x < 10) {
            x := x+1;
         }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x < 10
               THEN /\ x' = x+1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ x' = x

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Sun Mar 20 10:13:11 PDT 2011 by lamport
\* Created Sun Mar 20 10:10:54 PDT 2011 by lamport
